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
 *)

(* an detailed index of string in Append. 
 * (x, k) means the position of a k-th variable used in the assignment to x.
 *)
type_synonym 'y index = "'y \<times> nat"

(* Shuffle *)
type_synonym 'y shuffle = "'y \<Rightarrow> 'y list"

definition idS :: "'y shuffle" where
  "idS \<equiv> (\<lambda>y. [y])"

(* Store *)
type_synonym ('y, 'b) store = "'y index \<Rightarrow> 'b list"


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

(*
fun scan_pair2 where
  "scan_pair2 x [] = [(x, [])]" |
  "scan_pair2 x (Inl y#u) = (x, []) # scan_pair2 y u" |
  "scan_pair2 x (Inr a#u) = (case scan_pair2 x u of
     ((y, as)#pairs) \<Rightarrow> (y, a#as) # pairs)"

fun scan02 where
  "scan02 [] = ([], [])" |
  "scan02 (Inl x#u) = ([], scan_pair2 x u)" |
  "scan02 (Inr a#u) = (let (as, pair) = scan02 u in (a # as, pair))"
  
*)

fun scan_pair where
  "scan_pair x as [] = [(x, as)]" |
  "scan_pair x as (Inl y#u) = (x, as) # scan_pair y [] u" |
  "scan_pair x as (Inr a#u) = scan_pair x (as @ [a]) u"

fun scan0 where
  "scan0 as [] = (as, [])" |
  "scan0 as (Inl x#u) = (as, scan_pair x [] u)" |
  "scan0 as (Inr a#u) = scan0 (as @ [a]) u"
  
fun scan :: "('y + 'b) list \<Rightarrow> 'b list \<times> ('y \<times> 'b list) list" where
  "scan u = scan0 [] u"

fun flat_rec where
  "flat_rec [] = []" |
  "flat_rec ((x, as)#xas) = Inl x # map Inr as @ flat_rec xas"

fun flat where
  "flat (b0, xas) = map Inr b0 @ flat_rec xas"

fun replace_rec where
  "replace_rec y n [] = []" |
  "replace_rec y n ((x, _)#xs) = Inl x # Inr (y, n) # replace_rec y (Suc n) xs"

fun replace where
  "replace y (a0, xs) = Inr (y, 0) # replace_rec y 1 xs"

fun ith_string where
  "ith_string [] k = []" |
  "ith_string ((x,as)#xas) 0 = as" |
  "ith_string (_#xas) (Suc k) = ith_string xas k"



lemma flat_rec_scan_pair: "flat_rec (scan_pair x as u) = Inl x # map Inr as @ u"
  by (induct u arbitrary: x as rule: xa_induct, simp_all)

lemma flat_scan0: "flat (scan0 as u) = map Inr as @ u"
  by (induct u arbitrary: as rule: xa_induct, simp_all add: flat_rec_scan_pair)

lemma "flat (scan u) = u"
  by (induct u rule: xa_induct, simp_all add: flat_rec_scan_pair flat_scan0)


definition resolve_shuffle :: "('y, 'b) update \<Rightarrow> 'y shuffle" where
  "resolve_shuffle \<theta> y = extract_variables (\<theta> y)"

fun resolve_store :: "('y, 'b) update \<Rightarrow> ('y, 'b) store" where
  "resolve_store \<theta> (x, 0) = fst (scan (\<theta> x))" |
  "resolve_store \<theta> (x, k) = ith_string (snd (scan (\<theta> x))) k"


subsection \<open>Synthesize\<close>

definition synthesize_shuffle :: "'y shuffle \<Rightarrow> ('y, 'y index, 'b) update'" where
  "synthesize_shuffle s y = give_indices y (map Inl (s y))"

definition synthesize_prepend :: "('y, 'b) prepend \<Rightarrow> ('y, 'y, 'b) update'" where
  "synthesize_prepend a y = map Inr (a y) @ [Inl y]"

definition synthesize_append :: "('y, 'b) append \<Rightarrow> ('y index, 'y, 'b) update'" where
  "synthesize_append a = (\<lambda>(x, y, k). Inl y # map Inr (a (x, y, k)))"




definition synthesize :: "'y shuffle \<times> ('y, 'b) store \<Rightarrow> ('y, 'b) update" where
  "synthesize sap = (case sap of (s, a, p) \<Rightarrow>
     synthesize_append a \<bullet> synthesize_shuffle s \<bullet> synthesize_prepend p)"

fun lookup_store :: "('y, 'b) store \<Rightarrow> 'y location \<Rightarrow> 'b list" where
  "lookup_store (a, p) (Inl i) = a i" |
  "lookup_store (a, p) (Inr y) = p y"


subsection \<open>Properties of Decomposition\<close>

lemma give_indices_rec_Inr: "give_indices_rec k x (map Inr as @ xs) = map Inr as @ give_indices_rec k x xs"
  by (induct as, simp_all)

lemma hat_alpha_give_indices_left: "hat_alpha t (give_indices_rec k x u) = give_indices_rec k x (hat_alpha t u)"
proof (induct u arbitrary: k rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case by simp
next
  case (Alpha a xs)
  then show ?case by (simp add: give_indices_rec_Inr)
qed

lemma map_alpha_synthesize_append: "t \<star> synthesize_append a = synthesize_append (concat o map t o a)"
  by (auto simp add: synthesize_append_def map_alpha_def hat_alpha_right_map)

lemma map_alpha_synthesize_shuffle: "t \<star> synthesize_shuffle s = synthesize_shuffle s"
  by (rule ext, auto simp add: synthesize_shuffle_def map_alpha_def hat_alpha_right_map 
      hat_alpha_give_indices_left hat_alpha_left_ignore)

lemma map_alpha_synthesize_prepend: "t \<star> synthesize_prepend p = synthesize_prepend (concat o map t o p)"
  by (auto simp add: synthesize_prepend_def map_alpha_def hat_alpha_right_map)

lemma map_alpha_synthesize: "t \<star> synthesize (s, a, p) = synthesize (s, concat o map t o a, concat o map t o p)"
  by (simp add: synthesize_def map_alpha_distrib
      map_alpha_synthesize_shuffle map_alpha_synthesize_append map_alpha_synthesize_prepend)

lemma concat_map_resolve_append: "(concat o map t) (resolve_append \<theta> y) = resolve_append (t \<star> \<theta>) y"
  apply (simp add: resolve_append_def)

lemma resolve_idU_idS: "resolve_shuffle idU = idS"
  by (rule ext, simp add: idU_def idS_def resolve_shuffle_def)

theorem resolve_inverse: "synthesize (resolve m) x = m x"
  oops



















subsection \<open>Example\<close>

fun poyo :: "(int, char) update" where
  "poyo z = (if z = 0 then [Inr (CHR ''P''), Inl 0, Inr (CHR ''Q''), Inl 0, Inr (CHR ''R'')]
        else if z = 1 then [Inr (CHR ''A''), Inl 0, Inr (CHR ''B''), Inl 1, Inr (CHR ''C'')]
        else [])"

lemma "resolve_prepend poyo 0 = ''P''" by (simp add: resolve_prepend_def)
lemma "resolve_prepend poyo 1 = ''A''" by (simp add: resolve_prepend_def)

lemma "resolve_append poyo (0, 0, 0) = ''Q''" by (simp add: resolve_append_def)
lemma "resolve_append poyo (0, 0, 1) = ''R''" by (simp add: resolve_append_def)
lemma "resolve_append poyo (1, 0, 0) = ''B''" by (simp add: resolve_append_def)
lemma "resolve_append poyo (1, 1, 1) = ''C''" by (simp add: resolve_append_def)


lemma "resolve_shuffle poyo 0 = [0, 0]" by (simp add: resolve_shuffle_def)


(*
lemma "synthesize (resolve poyo) x = poyo x"
  by (simp add: synthesize_def resolve_def comp_def)

*)

end
