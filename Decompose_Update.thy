(* Title:   Decompose_Update.thy
   Author:  Akama Hitoshi
*)

section \<open>Decomposition of an Update\<close>

theory Decompose_Update
  imports Main Update
begin

(* an Update can be divided into two objects:
 * Shuffle (M\<^sup>1): shuffle and concatenate variables.
 * Append  (M\<^sup>2): append and prepend strings to variables.
 *)

(* an detailed index of string in Append. 
 * (x, y, k) means the k-th location of occurence of variable y in the assignment to x.
 *)
type_synonym 'y index = "'y \<times> 'y \<times> nat"

(* Shuffle *)
type_synonym 'y shuffle = "'y \<Rightarrow> ('y index) list"

(* Append *)
type_synonym ('y, 'b) append = "'y index \<Rightarrow> 'b list"

(* Prepend *)
type_synonym ('y, 'b) prepend = "'y \<Rightarrow> 'b list"


subsection \<open>Utility functions\<close>

(* obtain the first string (of alphabet) before any variable *)
fun first_string :: "('x + 'b) list \<Rightarrow> 'b list" where
  "first_string [] = []" |
  "first_string (Inl x#xs) = []" |
  "first_string (Inr b#xs) = b # first_string xs"

(* skip input characters until a variable specified occurs *)
fun skip_until :: "'y \<Rightarrow> ('y + 'b) list \<Rightarrow> ('y + 'b) list" where
  "skip_until y' [] = []" |
  "skip_until y' (Inl y0#xs) = 
    (if y' = y0 then xs else skip_until y' xs)" |
  "skip_until y' (Inr b#xs) = skip_until y' xs"


fun extract_variables :: "('x + 'b) list \<Rightarrow> 'x list" where
  "extract_variables [] = []" |
  "extract_variables (Inl x#xs) = x # extract_variables xs" |
  "extract_variables (Inr a#xs) = extract_variables xs"

(* increment the counter *)
fun increment :: "('x \<Rightarrow> nat) \<Rightarrow> 'x \<Rightarrow> ('x \<Rightarrow> nat)" where
  "increment cnt x = (\<lambda>y. if x = y then Suc (cnt x) else cnt x)"

fun give_indices_rec :: "('x \<Rightarrow> nat) \<Rightarrow> 'x \<Rightarrow> ('x + 'b) list \<Rightarrow> ('x index + 'b) list" where
  "give_indices_rec cnt x [] = []" |
  "give_indices_rec cnt x (Inl y#ys) = Inl (x, y, cnt y) # give_indices_rec (increment cnt y) x ys" |
  "give_indices_rec cnt x (Inr b#ys) = Inr b # give_indices_rec cnt x ys"

fun give_indices :: "'x \<Rightarrow> ('x + 'b) list \<Rightarrow> ('x index + 'b) list" where
  "give_indices x ys = give_indices_rec (\<lambda>y. 0) x ys"

subsection \<open>Resolve\<close>

fun resolve_shuffle :: "('y, 'b) update \<Rightarrow> 'y shuffle" where
  "resolve_shuffle \<theta> y = extract_variables (give_indices y (\<theta> y))"

fun resolve_prepend :: "('y, 'b) update \<Rightarrow> ('y, 'b) prepend" where
  "resolve_prepend \<theta> y = first_string (give_indices y (\<theta> y))"

fun resolve_append :: "('y, 'b) update \<Rightarrow> ('y, 'b) append" where
  "resolve_append \<theta> (x, y, k) = first_string (skip_until (x, y, k) (give_indices x (\<theta> x)))"

definition resolve :: "('y, 'b) update \<Rightarrow> 'y shuffle \<times> ('y, 'b) append \<times> ('y, 'b) prepend" where
  "resolve \<theta> = (resolve_shuffle \<theta>, resolve_append \<theta>, resolve_prepend \<theta>)"

subsection \<open>Synthesize\<close>

fun synthesize_shuffle :: "'y shuffle \<Rightarrow> ('y, 'y index, 'b) update'" where
  "synthesize_shuffle s y = map Inl (s y)"

fun synthesize_prepend :: "('y, 'b) prepend \<Rightarrow> ('y, 'y, 'b) update'" where
  "synthesize_prepend a y = map Inr (a y) @ [Inl y]"

fun synthesize_append :: "('y, 'b) append \<Rightarrow> ('y index, 'y, 'b) update'" where
  "synthesize_append a (x, y, k) = Inl y #  map Inr (a (x, y, k))"

definition synthesize :: "'y shuffle \<times> ('y, 'b) append \<times> ('y, 'b) prepend \<Rightarrow> ('y, 'b) update" where
  "synthesize sap = (case sap of (s, a, p) \<Rightarrow>
     synthesize_append a \<bullet> synthesize_shuffle s \<bullet> synthesize_prepend p)"

subsection \<open>Example\<close>

fun poyo :: "(int, char) update" where
  "poyo z = (if z = 0 then [Inr (CHR ''P''), Inl 0, Inr (CHR ''Q''), Inl 0, Inr (CHR ''R'')]
       else if z = 1 then [Inr (CHR ''A''), Inl 0, Inr (CHR ''B''), Inl 1, Inr (CHR ''C'')]
       else [])"

lemma "resolve_prepend poyo 0 = ''P''" by simp
lemma "resolve_prepend poyo 1 = ''A''" by simp

lemma "resolve_append poyo (0, 0, 0) = ''Q''" by simp
lemma "resolve_append poyo (0, 0, 1) = ''R''" by simp
lemma "resolve_append poyo (1, 0, 0) = ''B''" by simp
lemma "resolve_append poyo (1, 1, 0) = ''C''" by simp

lemma "resolve_shuffle poyo 0 = [(0, 0, 0), (0, 0, 1)]" by simp

lemma "synthesize (resolve poyo) x = poyo x" by (simp add: synthesize_def resolve_def comp_def)

end
