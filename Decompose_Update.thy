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


fun extract_variables :: "('x + 'b) list \<Rightarrow> 'x list" where
  "extract_variables [] = []" |
  "extract_variables (Inl x#xs) = x # extract_variables xs" |
  "extract_variables (Inr a#xs) = extract_variables xs"

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

fun padding_rec :: "nat \<Rightarrow> 'x \<Rightarrow> ('x \<times> 'b list) list \<Rightarrow> ('x + 'x index) list" where
  "padding_rec n y [] = []" |
  "padding_rec n y ((x, _)#xs) = Inl x # Inr (y, n) # padding_rec (Suc n) y xs"

fun padding where
  "padding y (a0, xs) = Inr (y, 0) # padding_rec 1 y xs"


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

definition resolve_shuffle :: "('y, 'b) update \<Rightarrow> 'y shuffle" where
  "resolve_shuffle \<theta> y = extract_variables (\<theta> y)"

definition resolve_store :: "('y, 'b) update \<Rightarrow> ('y, 'b) store" where
  "resolve_store \<theta> y = (case y of
     (x, 0) \<Rightarrow> fst (scan (\<theta> x)) |
     (x, Suc k) \<Rightarrow> ith_string (snd (scan (\<theta> x))) k)"

fun resolve :: "('y, 'b) update \<Rightarrow> 'y shuffle \<times> ('y, 'b) store" where
  "resolve \<theta> = (resolve_shuffle \<theta>, resolve_store \<theta>)"


subsection \<open>Synthesize\<close>

definition synthesize_shuffle :: "'y shuffle \<Rightarrow> ('y, 'y + 'y index, 'b) update'" where
  "synthesize_shuffle s y = map Inl (padding y (scan (map Inl (s y) :: ('y + 'y) list)))"

definition synthesize_store :: "('y, 'b) store \<Rightarrow> ('y + 'y index, 'y, 'b) update'" where
  "synthesize_store a yi = (case yi of
     (Inl y) \<Rightarrow> [Inl y] | 
     (Inr i) \<Rightarrow> map Inr (a i))"

fun synthesize :: "'y shuffle \<times> ('y, 'b) store \<Rightarrow> ('y, 'b) update" where
  "synthesize (s, a) = synthesize_store a \<bullet> synthesize_shuffle s"


subsection \<open>Properties of Decomposition\<close>

lemma ext_sum:
  assumes "\<And>l. f (Inl l) = g (Inl l)"
  assumes "\<And>r. f (Inr r) = g (Inr r)"
  shows "f = g"
proof
  fix x
  show "f x = g x" using assms by (cases x, simp_all)
qed

lemma map_alpha_synthesize_shuffle: "t \<star> synthesize_shuffle s = synthesize_shuffle s"
  by (auto simp add: map_alpha_def hat_alpha_left_ignore synthesize_shuffle_def)

lemma map_alpha_synthesize_store: "t \<star> synthesize_store p = synthesize_store (concat o map t o p)"
  by (rule ext_sum, simp_all add: map_alpha_def Update.hat_alpha_right_map synthesize_store_def)

lemma map_alpha_synthesize: "t \<star> synthesize (s, a) = synthesize (s, concat o map t o a)"
  by (auto simp add: map_alpha_distrib map_alpha_synthesize_shuffle map_alpha_synthesize_store)

lemma resolve_idU_idS: "resolve_shuffle idU = idS"
  by (auto simp add: idU_def idS_def resolve_shuffle_def)

theorem resolve_inverse: "synthesize (resolve m) x = m x"
  apply (simp add: comp_def)
  oops

















subsection \<open>Example\<close>

definition poyo :: "(int, char) update" where
  "poyo = (%z. if z = 0 then [Inr (CHR ''P''), Inl 0, Inr (CHR ''Q''), Inl 0, Inr (CHR ''R'')]
        else if z = 1 then [Inr (CHR ''A''), Inl 0, Inr (CHR ''B''), Inl 1, Inr (CHR ''C'')]
        else [])"

declare poyo_def [simp]

value "poyo 1"
value "resolve_store poyo (0, 2)"
value "resolve_store poyo (0, 3)"

lemma "resolve_shuffle poyo 0 = [0, 0]" by simp
lemma "resolve_shuffle poyo 1 = [0, 1]" by simp

lemma "resolve_store poyo (0, 0) = ''P''" by simp
lemma "resolve_store poyo (0, 1) = ''Q''" by simp
lemma "resolve_store poyo (0, 2) = ''R''" oops
lemma "resolve_store poyo (1, 0) = ''A''" by simp
lemma "resolve_store poyo (1, 1) = ''B''" by simp


lemma "synthesize (resolve poyo) x = poyo x"
  by (simp add: comp_def)


end
