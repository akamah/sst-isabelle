(* Title:   Decompose_Update.thy
   Author:  Akama Hitoshi
*)

section \<open>Decomposition of an Update\<close>

theory Decompose_Update
  imports Main Update List SST
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

(* extract only variables from var-alphabet list *)
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

(* scan var-alphabet list, build pairs of a variable and a string *)
definition scan :: "('y + 'b) list \<Rightarrow> 'b list \<times> ('y \<times> 'b list) list" where
  "scan u = scan0 [] u"

fun flat_rec where
  "flat_rec [] = []" |
  "flat_rec ((x, as)#xas) = Inl x # map Inr as @ flat_rec xas"


(* flatten pairs *)
definition flat where
  "flat = (\<lambda>(b0, xas). map Inr b0 @ flat_rec xas)"

fun padding_rec :: "nat \<Rightarrow> 'x \<Rightarrow> ('x \<times> 'b list) list \<Rightarrow> ('x + 'x index) list" where
  "padding_rec n y [] = []" |
  "padding_rec n y ((x, _)#xs) = Inl x # Inr (y, n) # padding_rec (Suc n) y xs"

(* replace strings a special meta-variable *)
definition padding :: "'y \<Rightarrow> 'b list \<times> ('y \<times> 'b list) list \<Rightarrow> ('y + 'y index) list" where
  "padding y = (\<lambda>(a0, xs). Inr (y, 0) # padding_rec 1 y xs)"


fun ith_string where
  "ith_string [] k = []" |
  "ith_string ((x,as)#xas) 0 = as" |
  "ith_string (_#xas) (Suc k) = ith_string xas k"


lemma ith_string_append_length: "ith_string (xs @ ys) (length xs) = ith_string ys 0"
  by (induct xs arbitrary: ys, simp_all)


definition flat_store where
  "flat_store xs yi = (case yi of
    (Inl y) \<Rightarrow> [Inl y] |
    (Inr (x, 0)) \<Rightarrow> map Inr (fst xs) |
    (Inr (x, Suc k)) \<Rightarrow> map Inr (ith_string (snd xs) k))"

lemma flat_rec_scan_pair: "flat_rec (scan_pair x as u) = Inl x # map Inr as @ u"
  by (induct u arbitrary: x as rule: xa_induct, simp_all)

lemma flat_scan0: "flat (scan0 as u) = map Inr as @ u"
  by (induct u arbitrary: as rule: xa_induct, simp_all add: flat_def flat_rec_scan_pair)

lemma scan_inverse: "flat (scan u) = u"
proof (induct u rule: xa_induct)
  case Nil
  then show ?case by (simp add: flat_def scan_def)
next
  case (Var x xs)
  then show ?case by (simp add: flat_def scan_def flat_rec_scan_pair)
next
  case (Alpha a xs)
  then show ?case by (simp add: flat_scan0 scan_def)
qed


subsection \<open>String version of resolve/synthesize proof\<close>


(*
fun fill_rec :: "'x \<Rightarrow> nat \<Rightarrow> 'x list \<Rightarrow> 'x index list" where
  "fill_rec x n [] = []" |
  "fill_rec x n (y#ys) = (x, n) # fill_rec x (Suc n) ys"

fun fill :: "'x \<Rightarrow> 'x list \<Rightarrow> 'x index list" where
  "fill x ys = (x, 0) # fill_rec x 1 ys"

fun lookup_rec where
  "lookup_rec [] n = []" | 
  "lookup_rec (as#_) 0 = as" |
  "lookup_rec (_#ws) (Suc k) = lookup_rec ws k"

fun lookup :: "('b list \<times> 'b list list) \<Rightarrow> 'x index \<Rightarrow> 'b list" where
  "lookup (b0, _) (x, 0) = b0" |
  "lookup (_, tab) (x, Suc k) = lookup_rec tab k"

fun split_rec where
  "split_rec as [] = [as]" |
  "split_rec as (Inr a#u) = split_rec (as @ [a]) u" |
  "split_rec as (Inl x#u) = as # split_rec [] u"

fun split_0 where
  "split_0 as [] = (as, [])" |
  "split_0 as (Inr a#u) = split_0 (as @ [a]) u" |
  "split_0 as (Inl x#u) = (as, split_rec [] u)"

fun split where
  "split u = split_0 [] u"

value "split [Inr (1 :: nat), Inl (0 :: nat), Inr 1, Inr 0]"
value "fill (0 :: nat) [0, 1, 2]"

lemma "concat (map (lookup_rec (split_rec [] u) k) (fill_rec x n x (extract_variables u))) = valuate u"


lemma "concat (map (lookup (split u)) (fill x (extract_variables u))) = valuate u"
proof (induct u rule: xa_induct)
case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case apply simp
next
  case (Alpha a xs)
  then show ?case sorry
qed
*)

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

(* \<pi> *)
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



lemma padding_rec_scan_pair_ignore_alphabets_0:
      "padding_rec n x (scan_pair y0 as (map Inl (extract_variables u))) 
     = padding_rec n x (scan_pair y0 bs u)"
  by (induct u arbitrary: n y0 as bs rule: xa_induct, simp_all)

lemma padding_rec_scan_pair_ignore_alphabets:
      "padding_rec n x (scan_pair y0 as (map Inl (extract_variables u))) 
     = padding_rec n x (scan_pair y0 [] u)"
  by (simp only: padding_rec_scan_pair_ignore_alphabets_0)

lemma padding_scan0_ignore_alphabet: "padding y (scan0 [a] xs) = padding y (scan0 [] xs)"
  by (induct xs rule: scan0.induct, simp_all add: padding_def)

lemma padding_scan_ignore_alphabet: "padding x (scan (map Inl (extract_variables u))) = padding x (scan u)"
proof (induct u rule: xa_induct)
  case Nil
  then show ?case by (simp add: scan_def padding_def)
next
  case (Var y xs)
  then show ?case by (simp add: scan_def padding_rec_scan_pair_ignore_alphabets padding_def)
next
  case (Alpha a xs)
  then show ?case by (simp add: scan_def padding_scan0_ignore_alphabet)
qed

lemma "synthesize_store (resolve_store m) (Inr (x, k)) = flat_store (scan (m x)) (Inr (x, k))"
  by (simp add: resolve_store_def synthesize_store_def flat_store_def Nitpick.case_nat_unfold)

lemma "synthesize_store (resolve_store m) (Inl y) = flat_store (scan (m x)) (Inl y)"
  by (simp add: resolve_store_def synthesize_store_def flat_store_def)

lemma synthesize_resolve_eq_flat:
  assumes "yi = Inl y \<or> yi = Inr (x, k)"
  shows "synthesize_store (resolve_store m) yi = flat_store (scan (m x)) yi"
proof (cases yi)
  case (Inl a)
  then show ?thesis by (simp add: resolve_store_def synthesize_store_def flat_store_def)
next
  case (Inr b)
  then have "yi = Inr (x, k)" using assms by simp
  then show ?thesis by (simp add: resolve_store_def synthesize_store_def flat_store_def Nitpick.case_nat_unfold)
qed

lemma padding_rec_x: "list_all (\<lambda>yi. (\<exists>y. yi = Inl y) \<or> (\<exists>k. yi = Inr (x, k))) (padding_rec n x xas)"
  by (induct xas rule: padding_rec.induct, simp_all)

lemma padding_x: "list_all (\<lambda>yi. (\<exists>y. yi = Inl y) \<or> (\<exists>k. yi = Inr (x, k))) (padding x xas)"
  by (cases xas, simp add: padding_rec_x padding_def)

lemma concat_map_synthesize_resolve_flat:
  assumes "list_all (\<lambda>yi. (\<exists>y. yi = Inl y) \<or> (\<exists>k. yi = Inr (x, k))) xs"
  shows "concat (map (synthesize_store (resolve_store m)) xs) = concat (map (flat_store (scan (m x))) xs)"
using assms proof (induct xs rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x u)
  then show ?case by (simp add: synthesize_resolve_eq_flat)
next
  case (Alpha a u)
  then show ?case using synthesize_resolve_eq_flat by force
qed


  
lemma concat_map_padding: 
  "concat (map (synthesize_store (resolve_store m)) (padding x xas)) =
   concat (map (flat_store (scan (m x))) (padding x xas))"
  apply (rule concat_map_synthesize_resolve_flat)
  apply (rule padding_x)
  done

lemma flat_rec_append[simp]: "flat_rec (xs @ ys) = flat_rec xs @ flat_rec ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by simp
next
  case (Cons xas xs)
  then show ?case proof (cases xas)
    case (Pair x as)
    then show ?thesis by (simp add: Cons)
  qed
qed


lemma flat_append[simp]: "flat (b0, xs @ ys) = flat (b0, xs) @ flat_rec ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by (simp add: flat_def)
next
  case (Cons xas xs)
  then show ?case proof (cases xas)
    case (Pair x as)
    then show ?thesis by (simp add: flat_def)
  qed
qed


lemma flat_store_padding_append: 
      "concat (map (flat_store (b0, xs @ ys)) (padding y (b0, xs @ ys)))
     = concat (map (flat_store (b0, xs)) (padding y (b0, xs))) 
       @ concat (map (flat_store (b0, xs @ ys)) 
                   (padding_rec (Suc (length xs)) y ys))"
proof (induct xs arbitrary: ys rule: rev_induct)
  case Nil
  then show ?case by (simp add: padding_def flat_store_def)
next
  case (snoc xas xs)
  show ?case proof (cases xas)
    case (Pair x as)
    then show ?thesis
      by (simp add: snoc, simp add: flat_store_def ith_string_append_length)
  qed
qed

lemma flat_store_flat0: "concat (map (flat_store (b0, xs)) (padding x (b0, xs))) = flat (b0, xs)"
proof (induct xs rule: rev_induct)
  case Nil
  then show ?case by (simp add: flat_store_def padding_def flat_def)
next
  case (snoc xas xs) then show ?case proof (cases xas)
    case (Pair y as)
    then show ?thesis apply (simp add: snoc flat_store_padding_append)
      apply (simp add: flat_store_def ith_string_append_length)
      done
  qed
qed

lemma flat_store_flat: "concat (map (flat_store scanned) (padding x scanned)) = flat scanned"
  by (cases scanned, simp add: flat_store_flat0)

theorem resolve_inverse: "synthesize (resolve m) x = m x"
  apply (simp add: comp_def synthesize_shuffle_def hat_hom_left_concat_map resolve_shuffle_def)
  apply (simp add: padding_scan_ignore_alphabet)
  apply (simp add: concat_map_padding)
  apply (simp add: flat_store_flat scan_inverse)
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
