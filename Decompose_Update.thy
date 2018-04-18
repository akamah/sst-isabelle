(* Title:   Decompose_Update.thy
   Author:  Akama Hitoshi
*)

section \<open>Decomposition of an Update\<close>

theory Decompose_Update
  imports Main Update List
begin

(* an Update can be divided into two objects:
 * Shuffle (M\<^sup>1): shuffle and concatenate variables.
 * Store   (M\<^sup>2): stores strings which'll be concatenated to variables:
 *   Append:  append
 *   Prepend: prepend
 *)

(* an detailed index of string in Append. 
 * (x, y, k) means the position of variable y,
    and its k-th occurence along all variables used in the assignment to x.
 *)
type_synonym 'y index = "'y \<times> 'y \<times> nat"

(* Shuffle *)
type_synonym 'y shuffle = "'y \<Rightarrow> ('y index) list"

definition idS :: "'y shuffle" where
  "idS \<equiv> (\<lambda>y. [(y, y, 0)])"

(* Append *)
type_synonym ('y, 'b) append = "'y index \<Rightarrow> 'b list"

(* Prepend *)
type_synonym ('y, 'b) prepend = "'y \<Rightarrow> 'b list"

(* Store *)
type_synonym ('y, 'b) store = "('y, 'b) append \<times> ('y, 'b) prepend"

(* location of store *)
type_synonym 'y location = "'y index + 'y"


subsection \<open>Utility functions\<close>

(* obtain the first string (of alphabet) before any variable *)
fun first_string :: "('x + 'b) list \<Rightarrow> 'b list" where
  "first_string [] = []" |
  "first_string (Inl x#xs) = []" |
  "first_string (Inr b#xs) = b # first_string xs"

(* skip input characters until a variable specified occurs *)
fun skip_until_var :: "('y + 'b) list \<Rightarrow> ('y + 'b) list" where
  "skip_until_var [] = []" |
  "skip_until_var (Inl x#xs) = xs" |
  "skip_until_var (Inr b#xs) = skip_until_var xs"

(* skip input characters until a variable specified occurs *)
fun skip_until :: "'y index \<Rightarrow> ('y index + 'b) list \<Rightarrow> ('y index + 'b) list" where
  "skip_until y' [] = []" |
  "skip_until (x, y, k) (Inl (x0, y0, k0)#xs) = 
    (if k = k0 then xs else skip_until (x, y, k) xs)" |
  "skip_until y' (Inr b#xs) = skip_until y' xs"

fun nth_string :: "nat \<Rightarrow> ('y + 'b) list \<Rightarrow> 'b list" where
  "nth_string 0 xs = first_string xs" |
  poyo: "nth_string (Suc n) xs = nth_string n (skip_until_var xs)"


fun extract_variables :: "('x + 'b) list \<Rightarrow> 'x list" where
  "extract_variables [] = []" |
  "extract_variables (Inl x#xs) = x # extract_variables xs" |
  "extract_variables (Inr a#xs) = extract_variables xs"

fun give_indices_rec :: "nat \<Rightarrow> 'x \<Rightarrow> ('x + 'b) list \<Rightarrow> ('x index + 'b) list" where
  "give_indices_rec cnt x [] = []" |
  "give_indices_rec cnt x (Inl y#ys) = Inl (x, y, cnt) # give_indices_rec (Suc cnt) x ys" |
  "give_indices_rec cnt x (Inr b#ys) = Inr b # give_indices_rec cnt x ys"

fun give_indices :: "'x \<Rightarrow> ('x + 'b) list \<Rightarrow> ('x index + 'b) list" where
  "give_indices x ys = give_indices_rec 0 x ys"

subsection \<open>Resolve\<close>

fun resolve_shuffle :: "('y, 'b) update \<Rightarrow> 'y shuffle" where
  "resolve_shuffle \<theta> y = extract_variables (give_indices y (\<theta> y))"

fun resolve_prepend :: "('y, 'b) update \<Rightarrow> ('y, 'b) prepend" where
  "resolve_prepend \<theta> y = first_string (\<theta> y)"

fun resolve_append :: "('y, 'b) update \<Rightarrow> ('y, 'b) append" where
  "resolve_append \<theta> (x, y, k) = first_string (skip_until (x, y, k) (give_indices x (\<theta> x)))"

(* useful function *) 
fun resolve_store :: "('y, 'b) update \<Rightarrow> ('y, 'b) store" where
  "resolve_store \<theta> = (resolve_append \<theta>, resolve_prepend \<theta>)"

definition resolve :: "('y, 'b) update \<Rightarrow> 'y shuffle \<times> ('y, 'b) store" where
  "resolve \<theta> = (resolve_shuffle \<theta>, (resolve_append \<theta>, resolve_prepend \<theta>))"

subsection \<open>Synthesize\<close>

fun synthesize_shuffle :: "'y shuffle \<Rightarrow> ('y, 'y index, 'b) update'" where
  "synthesize_shuffle s y = map Inl (s y)"

fun synthesize_prepend :: "('y, 'b) prepend \<Rightarrow> ('y, 'y, 'b) update'" where
  "synthesize_prepend a y = map Inr (a y) @ [Inl y]"

fun synthesize_append :: "('y, 'b) append \<Rightarrow> ('y index, 'y, 'b) update'" where
  "synthesize_append a (x, y, k) = Inl y # map Inr (a (x, y, k))"

definition synthesize :: "'y shuffle \<times> ('y, 'b) store \<Rightarrow> ('y, 'b) update" where
  "synthesize sap = (case sap of (s, a, p) \<Rightarrow>
     synthesize_append a \<bullet> synthesize_shuffle s \<bullet> synthesize_prepend p)"

fun lookup_store :: "('y, 'b) store \<Rightarrow> 'y location \<Rightarrow> 'b list" where
  "lookup_store (a, p) (Inl i) = a i" |
  "lookup_store (a, p) (Inr y) = p y"


subsection \<open>Properties of Decomposition\<close>

(* an induction rule for variable and alphabet list *)
(* [consumes n] to skip first n assumptions at induction phase *)
lemma xw_induct [consumes 0, case_names String VarString]:
  assumes str: "(\<And>w. P (map Inr w))"
  and  varstr: "(\<And>x w u. P u \<Longrightarrow> P (map Inr w @ [Inl x] @ u))"
  shows "P xs"
proof (induct xs rule: xa_induct)
  case Nil
  then show ?case
    by (metis list.map_disc_iff str)
next
  case (Var x xs)
  then show ?case
    by (metis Nil_is_map_conv append_Cons append_self_conv2 varstr)
next
  case (Alpha a xs)
  then show ?case sorry
qed

theorem resolve_inverse: "synthesize (resolve m) x = m x"
proof (induct "m x")
  case Nil
  then show ?case by (simp add: resolve_def synthesize_def comp_def)
next
  case (Cons a xa)
  then show ?case
    apply (simp add: resolve_def synthesize_def comp_def hat_hom_right_ignore)

  sorry

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
lemma "resolve_append poyo (1, 1, 1) = ''C''" by simp


lemma "resolve_shuffle poyo 0 = [(0, 0, 0), (0, 0, 1)]" by simp


(*
lemma "synthesize (resolve poyo) x = poyo x"
    apply (simp add: synthesize_def resolve_def comp_def)
*)


end
