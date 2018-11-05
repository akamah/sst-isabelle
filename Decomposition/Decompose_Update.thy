(* Title:   Decompose_Update.thy
   Author:  Akama Hitoshi
*)

section \<open>Decomposition of an Update\<close>

theory Decompose_Update
  imports Main HOL.Enum HOL.List
    "../Util/Enum_Nat" "../Util/Scan"
    "../Core/Update" "../Core/SST" 
    "../Single_Use/Single_Use"
    "../Decomposition/Shuffle"
begin

(* an Update can be divided into two objects:
 * Shuffle (M\<^sup>1): shuffle and concatenate variables.
 * Store   (M\<^sup>2): stores strings which'll be concatenated to variables:
 *)

(* This is a type of max scanned length given bounded count 'k.
 * if 'k is instance of enum class, this type represents type-level natural number
 * |'k| + 1
 *)

(* an index of string in Store.
 * (y, k) means the position of a k-th variable used in the assignment to y.
 *)
type_synonym ('y, 'k) index = "'y \<times> 'k option"

(* Store object is an array of string indexed with ('y, 'i) index *)
type_synonym ('y, 'i, 'b) store = "('y, 'i) index \<Rightarrow> 'b list"


subsection \<open>Resolve\<close>

text \<open>\<pi> in the thesis\<close>


fun orElse where
  "orElse None b = b" |
  "orElse (Some a) b = Some a"

lemma [simp]: "orElse a None = a"
  by (cases a, simp_all)

lemma orElse_assoc: "orElse (orElse a b) c = orElse a (orElse b c)"
proof (cases a)
  case None
  then show ?thesis by simp
next
  case A: (Some a)
  then show ?thesis proof (cases b)
    case None
    then show ?thesis by simp
  next
    case B: (Some b)
    then show ?thesis proof (cases c)
      case None
      then show ?thesis by simp
    next
      case C: (Some c)
      then show ?thesis by (simp add: A B C)
    qed
  qed
qed

lemma orElse_eq_Some:
  assumes "orElse x y = Some a"
  shows "x = Some a \<or> y = Some a"
proof (cases x)
  case None
  then show ?thesis using assms by simp
next
  case (Some a)
  then show ?thesis using assms by simp
qed

lemma option_if_Some_None_eq_Some:
  assumes "(if cond then Some a else None) = Some b"
  shows "a = b"
using assms by (cases cond, simp_all)

lemma option_if_None_Some_eq_Some:
  assumes "(if cond then None else Some a) = Some b"
  shows "a = b"
using assms by (cases cond, simp_all)

lemma option_if_Some_None_eq_None:
  assumes "(if cond then Some a else None) = None"
  shows "\<not>cond"
using assms by (cases cond, simp_all)

lemma option_if_None_Some_eq_None:
  assumes "(if cond then None else Some a) = None"
  shows "cond"
using assms by (cases cond, simp_all)


lemma extract_variables_pair_scan_pair: "extract_variables_pair (scan_pair u) = extract_variables u"
  by (induct u rule: xw_induct, simp_all)

fun seek :: "'y \<Rightarrow> 'y list \<Rightarrow> 'y list" where
  "seek y0 [] = []" |
  "seek y0 (y#ys) = (if y = y0 then ys else seek y0 ys)"

fun calc_position_rows where
  "calc_position_rows s [] x = 0" |
  "calc_position_rows s (y#ys) x = count_list (s y) x + calc_position_rows s ys x"

lemma calc_position_rows_eq_sum:
  assumes "distinct ys"
  shows "calc_position_rows s ys x = (\<Sum>y\<in>set ys. count_list (s y) x)"
  using assms by (induct ys, simp_all)


definition calc_position where
  "calc_position s ys xs x = count_list xs x + calc_position_rows s ys x"



fun lookup_row where
  "lookup_row s x0 k0 ys [] = None" |
  "lookup_row s x0 k0 ys ((x, as)#xas) = 
    (if x = x0 \<and> calc_position s ys (extract_variables_pair xas) x = k0 then Some as else lookup_row s x0 k0 ys xas)"

fun lookup_rec where
  "lookup_rec m x0 k0 [] = None" |
  "lookup_rec m x0 k0 (y#ys) = orElse (lookup_row (resolve_shuffle m) x0 k0 ys (scan_pair (m y)))
                                       (lookup_rec m x0 k0 ys)"

fun lookup :: "('y, 'x, 'b) update' \<Rightarrow> 'x \<Rightarrow> nat \<Rightarrow>'y list \<Rightarrow> 'b list" where
  "lookup m x0 k0 ys = (case lookup_rec m x0 k0 ys of
                          Some as \<Rightarrow> as |
                          None    \<Rightarrow> [])"


fun resolve_store_nat :: "('y::enum, 'b) update \<Rightarrow> ('y, nat, 'b) store" where  
  "resolve_store_nat m (y, None) = fst (scan (m y))" |
  "resolve_store_nat m (y, Some k) = lookup m y k (Enum.enum :: 'y list)"

definition resolve_store :: "'k::enum boundedness \<Rightarrow> ('y::enum, 'b) update \<Rightarrow> ('y, 'k::enum, 'b) store" where  
  "resolve_store B m yi = (case yi of
     (y, None)   \<Rightarrow> resolve_store_nat m (y, None) | 
     (y, Some k) \<Rightarrow> resolve_store_nat m (y, Some (enum_to_nat k)))"

fun empty_store :: "('y::enum, 'k, 'b) store" where
  "empty_store (y, k) = []"


subsection \<open>Synthesize\<close>
text \<open>inverse of \<pi> in the thesis\<close>

fun give_index_row_rec :: "('y \<Rightarrow> 'x list) \<Rightarrow> 'y list \<Rightarrow> 'x list \<Rightarrow> ('x + 'x \<times> nat option) list" where
  "give_index_row_rec s ys Nil    = []" |
  "give_index_row_rec s ys (x#xs) = Inl x # Inr (x, Some (calc_position s ys xs x)) # give_index_row_rec s ys xs"

fun give_index_row where
  "give_index_row s y ys xs = Inr (y, None) # give_index_row_rec s ys xs"


fun synthesize_shuffle_nat :: "'y::enum shuffle \<Rightarrow> 'y \<Rightarrow> ('y + 'y \<times> nat option) list" where
  "synthesize_shuffle_nat s y = give_index_row s y (seek y (Enum.enum :: 'y list)) (s y)"

fun enum_convert :: "'k::enum boundedness \<Rightarrow> 'y \<times> nat option \<Rightarrow> ('y \<times> 'k option) list" where
  "enum_convert B (y, None)   = [(y, None)]" |
  "enum_convert B (y, Some k) = [(y, Some (nat_to_enum k))]"

fun synthesize_shuffle :: "'k::enum boundedness \<Rightarrow> 'y::enum shuffle \<Rightarrow> ('y, 'y + 'y \<times> 'k option, 'b) update'" where
  "synthesize_shuffle B s y = map Inl (hat_alpha (enum_convert B) (synthesize_shuffle_nat s y))"


fun synthesize_store :: "'k::enum boundedness \<Rightarrow> ('y::enum, 'k, 'b) store \<Rightarrow> ('y + 'y \<times> 'k option, 'y, 'b) update'" where
  "synthesize_store B store (Inl y)      = [Inl y]" |
  "synthesize_store B store (Inr (y, k)) = map Inr (store (y, k))"

definition synthesize :: "'k::enum boundedness \<Rightarrow> 'y::enum shuffle \<times> ('y, 'k, 'b) store
                      \<Rightarrow> ('y, 'b) update" where
  "synthesize B sa = (case sa of (s, a) \<Rightarrow> synthesize_store B a \<bullet> synthesize_shuffle B s)"


subsection \<open>Properties of Decomposition\<close>


lemma map_alpha_synthesize_shuffle: "t \<star> synthesize_shuffle B s = synthesize_shuffle B s"
  by (rule ext, simp add: map_alpha_apply)

lemma map_alpha_synthesize_store: "t \<star> synthesize_store B p = synthesize_store B (t \<odot> p)"
  by (rule ext_sum, simp add: map_alpha_apply, rule prod.induct, simp add: map_alpha_apply compS_apply)


lemma map_alpha_synthesize: "t \<star> synthesize B (s, a) = synthesize B (s, t \<odot> a)"
  apply (rule ext, simp add: synthesize_def map_alpha_distrib)
  apply (simp add:  map_alpha_synthesize_shuffle map_alpha_synthesize_store)
  done

lemma resolve_idU_idS: "resolve_shuffle idU = idS"
  by (auto simp add: idU_def idS_def resolve_shuffle_def)

lemma lookup_row_idU:
  assumes "lookup_row (resolve_shuffle (idU :: ('y, 'b) update))
                    x0 k0 ys (scan_pair ((idU :: ('y, 'b) update) y)) = Some as"
  shows "as = []"
proof (cases "y = x0 \<and> calc_position (resolve_shuffle (idU :: ('y, 'b) update)) ys [] y = k0")
  case True
  then show ?thesis using assms by (auto simp add: idU_def)
next
  case False
  then show ?thesis proof -
    have "lookup_row (resolve_shuffle (idU :: ('y, 'b) update)) x0 k0 ys (scan_pair ((idU :: ('y, 'b) update) y)) = None"
      using False by (simp add: idU_def)
    then show ?thesis using assms by simp
  qed
qed

lemma lookup_rec_idU:
  assumes "lookup_rec (idU :: ('y, 'b) update) x0 k0 ys = Some as"
  shows "as = []"
using assms proof (induct ys)
  case Nil
  then show ?case by simp
next
  let ?idU = "idU::('y, 'b) update"
  case (Cons a ys)
  show ?case proof -
    thm Cons[simplified]
    let ?left = "lookup_row (resolve_shuffle ?idU) x0 k0 ys (scan_pair (?idU a))"
    let ?right= "lookup_rec ?idU x0 k0 ys"
    have "orElse ?left ?right = Some as" 
      using Cons by simp
    then have "?left = Some as \<or> ?right = Some as"
      by (rule orElse_eq_Some)
    then show ?thesis proof
      assume "?left = Some as"
      then show ?thesis by (rule lookup_row_idU)
    next
      assume "?right = Some as"
      then show ?thesis using Cons by simp
    qed
  qed
qed

lemma resolve_idU_empty:
  fixes B :: "'k::enum boundedness"
  shows "resolve_store B (idU :: ('y::enum, 'b) update) = empty_store"
  unfolding resolve_store_def
proof (rule ext_prod, auto simp add: option.case_eq_if)
  fix y :: "'y"
  show "fst (scan (idU y)) = []" unfolding idU_def by simp
next
  fix y :: "'y"
  show "fst (scan (idU y)) = []" unfolding idU_def by simp
next
  let ?idU = "idU :: ('y, 'b) update"
  fix y :: "'y" and k :: "'k" and as :: "'b list"
  assume "lookup_rec idU y (enum_to_nat k) enum_class.enum = Some as"
  then show "as = []" by (rule lookup_rec_idU)
qed


lemma resolve_shuffle_distrib_str: 
  "extract_variables (hat_hom \<phi> u) = concat (map (resolve_shuffle \<phi>) (extract_variables u))"
  by (induct u rule: xa_induct, simp_all add: resolve_shuffle_def)

lemma resolve_shuffle_distrib: "resolve_shuffle (\<phi> \<bullet> \<psi>) = resolve_shuffle \<phi> \<odot> resolve_shuffle \<psi>"
  by (rule ext, simp add: compU_apply resolve_shuffle_def resolve_shuffle_distrib_str compS_apply)

lemma resolve_shuffle_map_alpha: "resolve_shuffle (t \<star> m) = resolve_shuffle m"
proof -
  have *: "\<And>u. extract_variables (hat_alpha t u) = extract_variables u"
    by (induct_tac u rule: xa_induct, simp_all)
  show ?thesis by (rule ext, auto simp add: resolve_shuffle_def map_alpha_def *)
qed



lemma length_scanned_of_variable_count:
  fixes u :: "('x::finite + 'a) list"
  assumes "length (extract_variables u) = k"
  shows "length_scanned (scan u) = k + 1"
using assms proof (induct u arbitrary: k rule: xw_induct)
  case (Word w)
  then show ?case by simp
next
  case (VarWord x w u)
  then show ?case by (simp del: length_scanned.simps)
qed


lemma bounded_copy_length_scanned:
  fixes m :: "('x::finite, 'a) update"
  assumes "bounded k m"
  shows "length_scanned (scan (m x)) \<le> Suc (card (UNIV::'x set) * k)"
proof -
  have "length (extract_variables (m x)) \<le> card (UNIV::'x set) * k"
    using assms by (simp add: variable_count_in_bounded_update)
  then show ?thesis
    by (simp add: length_scanned_of_variable_count)
qed




fun store_resolve :: "'k::enum boundedness \<Rightarrow> ('y::enum, 'b) update \<Rightarrow> ('y + 'y \<times> 'k option) \<Rightarrow> ('y + 'b) list" where
  "store_resolve B m (Inl y) = [Inl y]" |
  "store_resolve B m (Inr (y, None))   = map Inr (fst (scan (m y)))" |
  "store_resolve B m (Inr (y, Some k)) = map Inr (lookup m y (enum_to_nat k) (Enum.enum :: 'y list))"

fun store_resolve_nat :: "('y::enum, 'b) update \<Rightarrow> ('y + 'y \<times> nat option) \<Rightarrow> ('y + 'b) list" where
  "store_resolve_nat m (Inl y) = [Inl y]" |
  "store_resolve_nat m (Inr (y, None))   = map Inr (fst (scan (m y)))" |
  "store_resolve_nat m (Inr (y, Some n)) = map Inr (lookup m y n (Enum.enum :: 'y list))"


lemma store_resolve_eq: "synthesize_store B (resolve_store B m) = store_resolve B m"
proof (rule ext_sum)
  show "\<And>l. synthesize_store B (resolve_store B m) (Inl l) = store_resolve B m (Inl l)"
    unfolding resolve_store_def by simp
next
  fix r
  show "synthesize_store B (resolve_store B m) (Inr r) = store_resolve B m (Inr r)"
  proof (cases "r")
    case (Pair a b)
    then show ?thesis proof (cases "b")
      case None
      then show ?thesis using Pair unfolding resolve_store_def by simp
    next
      case (Some c)
      then show ?thesis using Pair unfolding resolve_store_def by simp
    qed
  qed
qed


fun var_mark_less_than :: "nat \<Rightarrow> 'x + 'x \<times> nat option \<Rightarrow> bool" where
  "var_mark_less_than K yk = (\<forall>x0 k0. yk = Inr (x0, Some k0) \<longrightarrow> k0 < K)"


lemma there_exists_corresponding_string_inner:
  assumes "Inr (x0, Some k0) \<in> set (give_index_row s y ys (extract_variables_pair xas))"
  shows "\<exists>as. lookup_row s x0 k0 ys xas = Some as"
  using assms unfolding resolve_shuffle_def
  by (induct xas rule: pair_induct, auto)

lemma there_exists_corresponding_string:
  assumes "Inr (x0, Some k0) \<in> set (give_index_row (resolve_shuffle m) y0 ys (resolve_shuffle m y0))"
  shows "\<exists>as. lookup_row (resolve_shuffle m) x0 k0 ys (scan_pair (m y0)) = Some as"
  apply (rule there_exists_corresponding_string_inner)
  using assms
  apply (simp add: extract_variables_pair_scan_pair)
  apply (simp add: resolve_shuffle_def)
  done


lemma give_index_row_position_ge:
  assumes "Inr (x0, Some k0) \<in> set (give_index_row s y0 ys xs)"
  shows "k0 \<ge> calc_position_rows s ys x0"
using assms proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case using Cons by (cases "x = x0", auto simp add: calc_position_def)
qed

lemma give_index_row_position_lt:
  assumes "Inr (x0, Some k0) \<in> set (give_index_row s y0 ys xs)"
  shows "k0 < calc_position s ys xs x0"
using assms proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case using Cons by (cases "x = x0", auto simp add: calc_position_def)
qed

lemma lookup_row_position_lt_None:
  assumes "k0 < calc_position_rows s ys x0"
  shows "lookup_row s x0 k0 ys xas = None"
using assms proof (induct xas rule: pair_induct)
  case Nil
  then show ?case by simp
next
  case (PairCons x as xas)
  then show ?case proof (cases "x = x0")
    case True
    then show ?thesis using PairCons by (simp add: calc_position_def)
  next
    case False
    then show ?thesis using PairCons by simp
  qed
qed


lemma calc_position_rows_seek:
  assumes "y0 \<in> set ys"
  shows "calc_position s (seek y0 ys) (s y0) x0
       \<le> calc_position_rows s ys x0"
using assms proof (induct ys)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case proof (cases "y = y0")
    case True
    then show ?thesis unfolding calc_position_def by simp
  next
    case False
    then have "y0 \<in> set ys" using Cons.prems by simp
    then show ?thesis using False Cons.hyps by simp
  qed
qed

lemma previous_row_does_not_have_same_variable:
  assumes "y0 \<in> set ys"
  assumes "Inr (x0, Some k0) \<in> set (give_index_row (resolve_shuffle m) y0 (seek y0 ys) 
                                      (resolve_shuffle m y0))"
  shows "lookup_row (resolve_shuffle m) x0 k0 ys xs = None"
proof -
  let ?xs0 = "resolve_shuffle m y0"
  have "k0 < calc_position (resolve_shuffle m) (seek y0 ys) ?xs0 x0"
    using assms(2) by (rule give_index_row_position_lt)
  also have "... \<le> calc_position_rows (resolve_shuffle m) ys x0"
    using assms(1) by (rule calc_position_rows_seek)
  finally have "k0 < calc_position_rows (resolve_shuffle m) ys x0" .
  then show ?thesis
    by (rule lookup_row_position_lt_None)
qed

lemma inspect_only_this_row:
  assumes "y0 \<in> set ys"
  assumes "Inr (x0, Some k0) \<in> set (give_index_row (resolve_shuffle m) y0 (seek y0 ys)
                                                    (resolve_shuffle m y0))"
  shows "lookup_rec m x0 k0 ys
       = lookup_row (resolve_shuffle m) x0 k0 (seek y0 ys) (scan_pair (m y0))"
  using assms 
proof (induct ys)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case proof (auto)
    assume a: "y = y0"
    then have "\<exists>as. lookup_row (resolve_shuffle m) x0 k0 ys (scan_pair (m y0)) = Some as"
      using Cons by (simp add: there_exists_corresponding_string)
    then show "orElse (lookup_row (resolve_shuffle m) x0 k0 ys (scan_pair (m y0))) (lookup_rec m x0 k0 ys)
             = lookup_row (resolve_shuffle m) x0 k0 ys (scan_pair (m y0))"
      by auto
  next
    assume y: "y \<noteq> y0"
    then have y0: "y0 \<in> set ys" using Cons(2) by simp
    moreover have in_row: "Inr (x0, Some k0) \<in> set (give_index_row (resolve_shuffle m) y0 (seek y0 ys) 
                                                           (resolve_shuffle m y0))"
      using Cons(3) y by simp 
    ultimately have *: "lookup_rec m x0 k0 ys = lookup_row (resolve_shuffle m) x0 k0 (seek y0 ys) (scan_pair (m y0))"
      using Cons by simp
    have "lookup_row (resolve_shuffle m) x0 k0 ys (scan_pair (m y)) = None"
      using y0 in_row by (rule previous_row_does_not_have_same_variable)
    then show "orElse (lookup_row (resolve_shuffle m) x0 k0 ys (scan_pair (m y))) (lookup_rec m x0 k0 ys)
            =  lookup_row (resolve_shuffle m) x0 k0 (seek y0 ys) (scan_pair (m y0))"
      using * by simp
  qed
qed

lemma all_var_mark_less_than_position:
  fixes s :: "'y shuffle"
  assumes "y0 \<in> set ys"
  assumes "Inr (x0, Some k0) \<in> set (give_index_row s y0 (seek y0 ys) (s y0))"
  shows "k0 < calc_position_rows s ys x0"
proof -
  have "k0 < calc_position s (seek y0 ys) (s y0) x0"
    using assms(2)
    by (rule give_index_row_position_lt)
  also have "... \<le> calc_position_rows s ys x0"
    using assms(1) by (rule calc_position_rows_seek)
  finally show ?thesis .
qed

lemma bounded_shuffle_less_than_position:
  fixes s :: "'y::enum shuffle"
  assumes "bounded_shuffle K s"
  assumes "Inr (x0, Some k0) \<in> set (give_index_row s y0 (seek y0 (Enum.enum :: 'y list)) (s y0))"
  shows "k0 < K"
proof -
  let ?enum = "Enum.enum :: 'y list"
  have "y0 \<in> set ?enum"
    by (simp add: enum_UNIV)
  then have "k0 < calc_position_rows s ?enum x0"
    using assms(2) by (rule all_var_mark_less_than_position)
  also have "... = (\<Sum>y::'y\<in>UNIV. count_list (s y) x0)" proof -
    have "distinct ?enum" using enum_distinct by simp
    moreover have "set ?enum = UNIV" using enum_UNIV by simp
    ultimately show ?thesis by (simp add: calc_position_rows_eq_sum)
  qed
  also have "... \<le> K"
    using assms(1) unfolding bounded_shuffle_def by simp
  finally show ?thesis .
qed

lemma bounded_shuffle_var_mark_less_than:
  fixes s :: "'y::enum shuffle"
  assumes "bounded_shuffle K s"
  shows "list_all (var_mark_less_than K) (give_index_row s y0 (seek y0 (Enum.enum :: 'y list)) (s y0))"
proof (simp only: list_all_iff, rule ballI)
  fix yk
  assume contain: "yk \<in> set (give_index_row s y0 (seek y0 enum_class.enum) (s y0))"
  show "var_mark_less_than K yk" proof (auto)
    fix x0 k0
    assume "yk = Inr (x0, Some k0)"
    then have "Inr (x0, Some k0) \<in> set (give_index_row s y0 (seek y0 enum_class.enum) (s y0))"
      using contain by simp
    then show "k0 < K" using bounded_shuffle_less_than_position[OF assms] by simp
  qed
qed


lemma concat_map_store_resolve_nat:
  fixes B :: "'k::enum boundedness"
  assumes "boundedness B K"
  assumes "list_all (var_mark_less_than K) u"
  shows "concat (map (store_resolve B m) (hat_alpha (enum_convert B) u))
 = concat (map (store_resolve_nat m) u)"
using assms(2) proof (induct u rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case by simp
next
  case (Alpha yi xs)
  then show ?case proof (cases yi)
    case (Pair y kn)
    then show ?thesis proof (cases kn)
      case None
      then show ?thesis using Pair Alpha by simp
    next
      case (Some k)
      have "(k < length (Enum.enum :: 'k list))" using Alpha Pair Some assms(1)
        unfolding boundedness_def by simp
      then have "enum_to_nat (nat_to_enum k :: 'k) = k" by (rule nat_enum_iso)
      then show ?thesis using Alpha by (simp add: Some Pair)
    qed
  qed
qed

lemma concat_map_store_resolve_give_index_row:
  fixes B :: "'k::enum boundedness"
  fixes m :: "('y::enum, 'b) update"
  assumes "boundedness B K"
  assumes "bounded K m"
  shows "concat (map (store_resolve B m) (hat_alpha (enum_convert B)
            (give_index_row (resolve_shuffle m) y0 (seek y0 (Enum.enum :: 'y list))
                            (resolve_shuffle m y0))))
       = concat (map (store_resolve_nat m) 
            (give_index_row (resolve_shuffle m) y0 (seek y0 (Enum.enum :: 'y list))
                            (resolve_shuffle m y0)))"
proof -
  have "bounded_shuffle K (resolve_shuffle m)"
    using assms(2) by (rule resolve_bounded)
  then have "list_all (var_mark_less_than K) (give_index_row (resolve_shuffle m) y0 (seek y0 (Enum.enum :: 'y list)) ((resolve_shuffle m) y0))"
    by (rule bounded_shuffle_var_mark_less_than)
  then show ?thesis
    using assms(1) using concat_map_store_resolve_nat by blast
qed



theorem resolve_inverse:
  fixes B :: "'k::enum boundedness"
  fixes m :: "('y::enum, 'b) update"
  assumes "boundedness B k"
  assumes "bounded k m"
  shows "synthesize B (resolve_shuffle m, resolve_store B m) = m"
  apply (rule ext)
  apply (simp add: synthesize_def)
  apply (simp add: compU_apply store_resolve_eq del: give_index_row.simps)
  apply (simp add: concat_map_store_resolve_give_index_row[OF assms] del: give_index_row.simps)

lemma extract_variables_synthesize_store: "extract_variables (concat (map (synthesize_store B a) u)) = extract_variables u"
  by (induct u rule: xa_induct, simp_all add: synthesize_store_def)

lemma extract_variables_padding_scan: "extract_variables (padding B x (scan (map Inl u))) = u"
proof (induct u rule: rev_induct)
  case Nil
  then show ?case by (simp add: scan_def synthesize_store_def)
next
  case (snoc x xs)
  then show ?case by (simp add: )
qed


theorem synthesize_inverse_shuffle: "resolve_shuffle (synthesize B (s, a)) = s"
  by (auto simp add: synthesize_def resolve_shuffle_def compU_apply
                     extract_variables_synthesize_store extract_variables_padding_scan)

lemma synthesize_prepend_idU: "synthesize_prepend B empty_store = idU"
  by (rule ext, simp add: idU_def)

lemma synthesize_idU: "synthesize B (idS :: 'x \<Rightarrow> 'x list, empty_store) = (idU :: ('x::enum, 'a) update)"
  apply (auto simp add: synthesize_def idU_def idS_def scan_def compU_apply synthesize_prepend_idU)

subsection \<open>Example\<close>

definition poyo :: "(bool, char) update" where
  "poyo = (%z. if z = False then [Inr (CHR ''P''), Inl False, Inr (CHR ''Q''), Inl False, Inr (CHR ''R'')]
        else if z = True then [Inr (CHR ''A''), Inl False, Inr (CHR ''B''), Inl True, Inr (CHR ''C'')]
        else [])"

declare poyo_def [simp]

definition testB :: "bool boundedness" where
  "testB = Type_Nat"


lemma "resolve_store testB poyo (False, None) = ''P''"
  by (simp add: resolve_store_def scan_def enum_to_nat_def enum_option_def enum_prod_def enum_bool_def)
  
lemma "resolve_store testB poyo (False, Some (False, False)) = ''Q''"
  by (simp add: resolve_store_def scan_def enum_to_nat_def enum_option_def enum_prod_def enum_bool_def)

lemma "resolve_store testB poyo (False, Some (False, True)) = ''R''" 
  by (simp add: resolve_store_def scan_def enum_to_nat_def enum_option_def enum_prod_def enum_bool_def)

lemma "resolve_store testB poyo (True, None) = ''A''"
  by (simp add: resolve_store_def scan_def enum_to_nat_def enum_option_def enum_prod_def enum_bool_def)

lemma "resolve_store testB poyo (True, Some (False, False)) = ''B''"
  by (simp add: resolve_store_def scan_def enum_to_nat_def enum_option_def enum_prod_def enum_bool_def)

lemma "resolve_store testB poyo (True, Some (False, True)) = ''C''" 
  by (simp add: resolve_store_def scan_def enum_to_nat_def enum_option_def enum_prod_def enum_bool_def)


end
