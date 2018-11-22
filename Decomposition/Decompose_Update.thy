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

text \<open>
  An Update can be divided into two objects:
 - Shuffle (M1): shuffle and concatenate variables.
 - Store   (M2): stores strings which'll be concatenated to variables:
\<close>

text \<open>
  An index of string in Store.
  Both 'y and 'k are required to be an enum class.
  - 'y is the type of variables, and should be enumerated.
  - 'k is the type-level natural number, the boundedness of an update.
\<close>
type_synonym ('y, 'k) index = "'y \<times> 'k option"


text \<open>
  Consider an update which has k occurrences of each variable, 
  it also has k + 1 strings between variables.
  So the type "'k option" is used to specify (k+1) indexes of strings.
  - (y, None) means the first string of the assignment to y.
  - (y, Some k) means the following string of k-th occurrence of x.
  Note that the occurrence is counted along bottom-up direction from zero.
  Example: 
    x \<mapsto> (x, None) x (x, Some 2) x (x, Some 1)
    y \<mapsto> (y, None) x (y, Some 0) y (y, Some 0)
\<close>
type_synonym ('y, 'i, 'b) store = "('y, 'i) index \<Rightarrow> 'b list"

subsection \<open>Utility functions\<close>


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

lemma map_option_orElse:
  "map_option f (orElse a b) = orElse (map_option f a) (map_option f b)"
  by (cases a, simp_all)


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

fun orNil :: "'a list option \<Rightarrow> 'a list" where
  "orNil (Some xs) = xs" |
  "orNil None      = []"

fun seek :: "'y \<Rightarrow> 'y list \<Rightarrow> 'y list" where
  "seek y0 [] = []" |
  "seek y0 (y#ys) = (if y = y0 then ys else seek y0 ys)"


subsection \<open>Auxiliary functions\<close>

fun calc_index_rows where
  "calc_index_rows s [] x = 0" |
  "calc_index_rows s (y#ys) x = count_list (s y) x + calc_index_rows s ys x"

lemma calc_index_rows_eq_sum:
  assumes "distinct ys"
  shows "calc_index_rows s ys x = (\<Sum>y\<in>set ys. count_list (s y) x)"
  using assms by (induct ys, simp_all)

definition calc_index where
  "calc_index s ys xs x = count_list xs x + calc_index_rows s ys x"


fun lookup_row where
  "lookup_row s x0 k0 ys [] = None" |
  "lookup_row s x0 k0 ys ((x, as)#xas) = 
    (if x = x0 \<and> calc_index s ys (keys_pair xas) x = k0 then Some as else lookup_row s x0 k0 ys xas)"

fun lookup_rec where
  "lookup_rec m x0 k0 [] = None" |
  "lookup_rec m x0 k0 (y#ys) = orElse (lookup_row (resolve_shuffle m) x0 k0 ys (scan_pair (m y)))
                                       (lookup_rec m x0 k0 ys)"

fun lookup :: "('y, 'x, 'b) update' \<Rightarrow> 'x \<Rightarrow> nat \<Rightarrow>'y list \<Rightarrow> 'b list" where
  "lookup m x0 k0 ys = orNil (lookup_rec m x0 k0 ys)"


fun give_index_row :: "('y \<Rightarrow> 'x list) \<Rightarrow> 'y list \<Rightarrow> 'x list \<Rightarrow> ('x + 'x \<times> nat option) list" where
  "give_index_row s ys Nil    = []" |
  "give_index_row s ys (x#xs) = Inl x # Inr (x, Some (calc_index s ys xs x)) # give_index_row s ys xs"

fun post_index_vars :: "('y \<Rightarrow> 'x list) \<Rightarrow> 'y list \<Rightarrow> 'x list \<Rightarrow> ('x \<times> nat) list" where
  "post_index_vars s ys Nil    = []" |
  "post_index_vars s ys (x#xs) = (x, calc_index s ys xs x) # post_index_vars s ys xs"


fun enum_convert :: "'k::enum boundedness \<Rightarrow> 'y \<times> nat option \<Rightarrow> ('y \<times> 'k option) list" where
  "enum_convert B (y, None)   = [(y, None)]" |
  "enum_convert B (y, Some k) = [(y, Some (nat_to_enum k))]"


lemma give_index_row_post_index_vars[iff]:
  "Inr (x0, Some k0) \<in> set (give_index_row s ys xs) \<longleftrightarrow>
       (x0, k0) \<in> set (post_index_vars s ys xs)"
  by (induct xs, auto)

lemma valuate_give_index_row_post_index_vars[iff]:
  "(x0, Some k0) \<in> set (valuate (give_index_row s ys xs)) \<longleftrightarrow>
   (x0, k0) \<in> set (post_index_vars s ys xs)"
 by (induct xs, auto)


subsection \<open>Resolve & Synthesize\<close>


lemma keys_pair_scan_pair: "keys_pair (scan_pair u) = extract_variables u"
  by (induct u rule: xw_induct, simp_all)

lemma concat_value_scanned_scan: "concat_value_scanned (scan u) = valuate u"
  by (induct u rule: xw_induct, simp_all)

fun resolve_store_nat :: "('y::enum, 'b) update \<Rightarrow> ('y, nat, 'b) store" where  
  "resolve_store_nat m (y, None) = fst (scan (m y))" |
  "resolve_store_nat m (y, Some k) = lookup m y k (Enum.enum :: 'y list)"

definition resolve_store :: "'k::enum boundedness \<Rightarrow> ('y::enum, 'b) update \<Rightarrow> ('y, 'k::enum, 'b) store" where  
  "resolve_store B m yi = (case yi of
     (y, None)   \<Rightarrow> resolve_store_nat m (y, None) | 
     (y, Some k) \<Rightarrow> resolve_store_nat m (y, Some (enum_to_nat k)))"

fun empty_store :: "('y::enum, 'k, 'b) store" where
  "empty_store (y, k) = []"


definition synthesize_shuffle_nat :: "'y::enum shuffle \<Rightarrow> 'y \<Rightarrow> ('y + 'y \<times> nat option) list" where
  "synthesize_shuffle_nat s y = Inr (y, None) # give_index_row s (seek y (Enum.enum :: 'y list)) (s y)"

fun synthesize_shuffle :: "'k::enum boundedness \<Rightarrow> 'y::enum shuffle \<Rightarrow> ('y, 'y + 'y \<times> 'k option, 'b) update'" where
  "synthesize_shuffle B s y = map Inl (hat_alpha (enum_convert B) (synthesize_shuffle_nat s y))"


fun synthesize_store :: "'k::enum boundedness \<Rightarrow> ('y::enum, 'k, 'b) store \<Rightarrow> ('y + 'y \<times> 'k option, 'y, 'b) update'" where
  "synthesize_store B store (Inl y)      = [Inl y]" |
  "synthesize_store B store (Inr (y, k)) = map Inr (store (y, k))"

definition synthesize :: "'k::enum boundedness \<Rightarrow> 'y::enum shuffle \<times> ('y, 'k, 'b) store
                      \<Rightarrow> ('y, 'b) update" where
  "synthesize B sa = (case sa of (s, a) \<Rightarrow> synthesize_store B a \<bullet> synthesize_shuffle B s)"


lemma index_cases [case_names VarNone VarSome]:
  assumes "\<And>y. yk = (y, None) \<Longrightarrow> P"
  assumes "\<And>y k. yk = (y, Some k) \<Longrightarrow> P"
  shows "P"
proof (cases yk)
  case (Pair y k)
  then show ?thesis using assms by (cases k, simp_all)
qed

lemma var_index_cases [case_names Var VarNil VarSome]:
  assumes Var:     "(\<And>y.   x = Inl y        \<Longrightarrow> P)"
  assumes VarNil:  "(\<And>y.   x = Inr (y, None) \<Longrightarrow> P)"
  assumes VarSome: "(\<And>y k. x = Inr (y, Some k)   \<Longrightarrow> P)"
  shows "P"
proof (cases x)
  case (Inl y)
  then show ?thesis using Var by simp
next
  case (Inr yk)
  then show ?thesis proof (cases yk)
    case (Pair y k)
    then show ?thesis proof (cases k)
      case None
      then show ?thesis using Inr Pair VarNil by simp
    next
      case (Some k)
      then show ?thesis using Inr Pair VarSome by simp
    qed
  qed
qed


subsection \<open>Properties of Resolve & Synthesize\<close>


lemma map_alpha_synthesize:
  "t \<star> synthesize B (s, a) = synthesize B (s, t \<odot> a)"
proof -
  have map_alpha_synthesize_shuffle: "t \<star> synthesize_shuffle B s = synthesize_shuffle B s"
    by (rule ext, simp add: map_alpha_apply)
  have map_alpha_synthesize_store: "t \<star> synthesize_store B a = synthesize_store B (t \<odot> a)"
    by (rule ext_sum, simp add: map_alpha_apply, rule prod.induct, simp add: map_alpha_apply compS_apply)
  show ?thesis
    by (rule ext, simp add: synthesize_def map_alpha_distrib map_alpha_synthesize_shuffle map_alpha_synthesize_store)
qed


lemma resolve_idU_idS: "resolve_shuffle idU = idS"
  by (rule ext, simp add: idU_def idS_def resolve_shuffle_def)

lemma resolve_idU_empty:
  fixes B :: "'k::enum boundedness"
  shows "resolve_store B (idU :: ('y::enum, 'b) update) = empty_store"
proof -
  { fix yk
    have "resolve_store B (idU :: ('y::enum, 'b) update) yk = empty_store yk"
    proof (cases yk rule: index_cases)
      case (VarNone y)
      then show ?thesis by (simp add: resolve_store_def idU_def)
    next
      case (VarSome y k)
      show ?thesis proof -
        { fix k' ys
          have "orNil (lookup_rec (idU :: ('y::enum, 'b) update) y k' ys) = []"
            by (induct ys, simp_all add: idU_def)
        }
        then show ?thesis by (simp add: resolve_store_def VarSome)
      qed
    qed
  } note that = this
  show ?thesis by (rule ext, simp add: that)
qed

lemma resolve_shuffle_distrib: "resolve_shuffle (\<phi> \<bullet> \<psi>) = resolve_shuffle \<phi> \<odot> resolve_shuffle \<psi>"
proof -
  have *: "\<And>u. extract_variables (hat_hom \<phi> u) = concat (map (resolve_shuffle \<phi>) (extract_variables u))"
    by (induct_tac u rule: xa_induct, simp_all add: resolve_shuffle_def)
  show ?thesis by (rule ext, simp add: compU_apply resolve_shuffle_def * compS_apply)
qed

lemma resolve_shuffle_map_alpha: "resolve_shuffle (t \<star> m) = resolve_shuffle m"
proof -
  have *: "\<And>u. extract_variables (hat_alpha t u) = extract_variables u"
    by (induct_tac u rule: xa_induct, simp_all)
  show ?thesis by (rule ext, auto simp add: resolve_shuffle_def map_alpha_def *)
qed


theorem synthesize_inverse_shuffle: "resolve_shuffle (synthesize B (s, a)) = s"
proof -
  { fix u
    have "extract_variables (concat (map (synthesize_store B a) u)) = extract_variables u"
    proof (induct u rule: xa_induct)
      case Nil
      then show ?case by simp
    next
      case (Var x xs)
      then show ?case by simp
    next
      case (Alpha yk xs)
      then show ?case proof (cases yk)
        case (Pair y k)
        then show ?thesis using Alpha by (cases k, simp_all)
      qed 
    qed
  } note 1 = this
  { fix x xs
    have "extract_variables (hat_alpha (enum_convert B) (give_index_row s (seek x enum_class.enum) xs)) = xs"
      by (induct xs, simp_all)
  } note 2 = this
  show ?thesis
    by (rule ext, simp add: synthesize_def compU_apply resolve_shuffle_def 1 2 synthesize_shuffle_nat_def)
qed

lemma synthesize_idU: "synthesize B (idS :: 'x shuffle, empty_store) = (idU :: ('x::enum, 'a) update)"
  by (rule ext, simp add: synthesize_def idU_def idS_def scan_def compU_apply synthesize_shuffle_nat_def)


lemma compS_resolve_store:
  fixes \<theta> :: "('y::enum, 'b) update"
  shows "s \<odot> resolve_store B \<theta> = resolve_store B (s \<star> \<theta>)"
proof
  fix yk
  show "(s \<odot> resolve_store B \<theta>) yk = resolve_store B (s \<star> \<theta>) yk"
  proof (cases yk rule: index_cases)
    case (VarNone y)
    show ?thesis proof (simp add: compS_apply resolve_store_def map_alpha_apply VarNone)
      fix u :: "('y + 'b) list"
      show "concat (map s (fst (scan u))) = fst (scan (hat_alpha s u))"
        by (induct u rule: xw_induct, simp_all)
    qed
  next
    case (VarSome y k)
    then show ?thesis proof (simp add: compS_apply resolve_store_def map_alpha_apply)
      fix ys k
      show "concat (map s (orNil (lookup_rec \<theta> y k ys)))
          = orNil (lookup_rec (s \<star> \<theta>) y k ys)" proof -
        have "concat (map s (orNil (lookup_rec \<theta> y k ys)))
            = orNil (map_option (concat o map s) (lookup_rec \<theta> y k ys))"
          by (cases "(lookup_rec \<theta> y k ys)", simp_all)
        also have "... = orNil (lookup_rec (s \<star> \<theta>) y k ys)"
        proof (rule arg_cong[where f="orNil"], induct ys)
          case Nil
          then show ?case by simp
        next
          case (Cons a ys)
          show ?case proof -
            { fix xas
              have "map_option (concat o map s) (lookup_row (resolve_shuffle \<theta>) y k ys xas)
                  = lookup_row (resolve_shuffle (s \<star> \<theta>)) y k ys (map_value_pair s xas)"
              proof (induct xas rule: pair_induct)
                case Nil
                then show ?case by simp
              next
                case (PairCons x as xas)
                then show ?case by (auto simp add: resolve_shuffle_map_alpha keys_pair_map_value_pair)
              qed
            } note map_option_lookup_rec = this
            { fix u :: "('y + 'b) list"
              have "map_value_pair s (scan_pair u) = scan_pair (hat_alpha s u)"
                by (induct u rule: xw_induct, simp_all)
            } note map_value_pair_scan_pair = this
            show ?thesis
              by (simp add: map_option_orElse map_option_lookup_rec Cons map_value_pair_scan_pair map_alpha_apply[symmetric] del: comp_apply)
          qed
        qed
        finally show ?thesis .
      qed
    qed
  qed
qed

lemma resolve_store_preserve_prop_on_string:
  fixes m :: "('x::enum, 'b) update"
  assumes "\<forall>x. list_all P (valuate (m x))"
  shows "\<forall>x k. list_all P (resolve_store B m (x, k))"
proof (intro allI)
  fix x0 k0
  have *: "\<forall>x. list_all P (concat_value_scanned (scan (m x)))"
    using assms by (simp add: concat_value_scanned_scan)

  show "list_all P (resolve_store B m (x0, k0))" proof (cases k0)
    case None
    have "list_all P (concat_value_scanned (scan (m x0)))"
      using * by simp
    then show ?thesis proof (simp add: None resolve_store_def)
      fix sc :: "('x, 'b) scanned"
      assume "list_all P (concat_value_scanned sc)"
      then show "list_all P (fst sc)"
       by (induct sc rule: scanned_rev_induct, simp_all)
    qed
  next
    case (Some k)
    then show ?thesis proof (simp add: resolve_store_def) 
      fix ys n
      show "list_all P (orNil (lookup_rec m x0 n ys))" proof (induct ys)
        case Nil
        then show ?case by simp
      next
        case (Cons y ys)
        then show ?case 
        proof (cases "lookup_row (resolve_shuffle m) x0 n ys (scan_pair (m y))")
          case None
          then show ?thesis using Cons by simp
        next
          case (Some as)
          have "list_all P (concat_value_pair (scan_pair (m y)))"
            using * unfolding concat_value_scanned_def by simp
          then show ?thesis using Some proof (simp)
            fix xas :: "('x \<times> 'b list) list" and s
            assume "list_all P (concat_value_pair xas)"
            moreover assume "lookup_row s x0 n ys xas = Some as"
            ultimately show "list_all P as" proof (induct xas rule: pair_induct)
              case Nil
              then show ?case by simp
            next
              case (PairCons x bs xas)
              then show ?case proof (cases "x = x0 \<and> calc_index s ys (keys_pair xas) x = n")
                case True
                then show ?thesis using PairCons by (simp add: True)
              next
                case False
                then show ?thesis using PairCons by (simp add: False)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma synthesize_preserve_prop_on_string:
  assumes "\<forall>x k. list_all P (a (x, k))"
  shows "\<forall>x. list_all P (valuate (synthesize B (s, a) x))"
proof (auto simp add: synthesize_def compU_def synthesize_shuffle_nat_def)
  fix x
  show "list_all P (a (x, None))" using assms by simp
next
  fix x u
  show "list_all P (valuate (concat (map (synthesize_store B a) u)))"
  proof (induct u rule: xa_induct)
    case Nil
    then show ?case by simp
  next
    case (Var x xs)
    then show ?case by simp
  next
    case (Alpha a xs)
    then show ?case using assms by (cases a, simp)
  qed
qed



lemma map_alpha_resolve_store:
  "t \<bullet> resolve_store B \<theta> = resolve_store B (update2hom t \<star> \<theta>)"
  by (simp add: update2hom_compS_compU[symmetric] compS_resolve_store)


subsection \<open>Proof of inverse of Resolve\<close>


fun var_index_less_than :: "nat \<Rightarrow> 'x + 'x \<times> nat option \<Rightarrow> bool" where
  "var_index_less_than K yk = (\<forall>x0 k0. yk = Inr (x0, Some k0) \<longrightarrow> k0 < K)"


lemma there_exists_corresponding_string_inner:
  assumes "(x0, k0) \<in> set (post_index_vars s ys (keys_pair xas))"
  shows "\<exists>as. lookup_row s x0 k0 ys xas = Some as"
  using assms unfolding resolve_shuffle_def
  by (induct xas rule: pair_induct, auto)

lemma there_exists_corresponding_string:
  assumes "(x0, k0) \<in> set (post_index_vars (resolve_shuffle m) ys (resolve_shuffle m y0))"
  shows "\<exists>as. lookup_row (resolve_shuffle m) x0 k0 ys (scan_pair (m y0)) = Some as"
  apply (rule there_exists_corresponding_string_inner)
  using assms
  apply (simp add: keys_pair_scan_pair)
  apply (simp add: resolve_shuffle_def)
  done

lemma there_doesnt_exist_corresponding_string_inner:
  assumes "(x0, k0) \<notin> set (post_index_vars s ys (keys_pair xas))"
  shows "lookup_row s x0 k0 ys xas = None"
  using assms unfolding resolve_shuffle_def
  by (induct xas rule: pair_induct, auto)

lemma there_doesnt_exist_corresponding_string:
  assumes "(x0, k0) \<notin> set (post_index_vars (resolve_shuffle m) ys (resolve_shuffle m y0))"
  shows "lookup_row (resolve_shuffle m) x0 k0 ys (scan_pair (m y0)) = None"  
  apply (rule there_doesnt_exist_corresponding_string_inner)
  using assms
  apply (simp add: keys_pair_scan_pair)
  apply (simp add: resolve_shuffle_def)
  done

lemma give_index_row_position_ge:
  assumes "(x0, k0) \<in> set (post_index_vars s ys xs)"
  shows "k0 \<ge> calc_index_rows s ys x0"
using assms proof (induct xs)
  case Nil
  then show ?case by (simp)
next
  case (Cons x xs)
  then show ?case using Cons by (cases "x = x0", auto simp add: calc_index_def)
qed

lemma give_index_row_position_lt:
  assumes "(x0, k0) \<in> set (post_index_vars s ys xs)"
  shows "k0 < calc_index s ys xs x0"
using assms proof (induct xs)
  case Nil
  then show ?case by (simp)
next
  case (Cons x xs)
  then show ?case using Cons by (cases "x = x0", auto simp add: calc_index_def)
qed

lemma lookup_row_position_lt_None:
  assumes "k0 < calc_index_rows s ys x0"
  shows "lookup_row s x0 k0 ys xas = None"
using assms proof (induct xas rule: pair_induct)
  case Nil
  then show ?case by simp
next
  case (PairCons x as xas)
  then show ?case proof (cases "x = x0")
    case True
    then show ?thesis using PairCons by (simp add: calc_index_def)
  next
    case False
    then show ?thesis using PairCons by simp
  qed
qed


lemma calc_index_rows_seek:
  assumes "y0 \<in> set ys"
  shows "calc_index s (seek y0 ys) (s y0) x0
       \<le> calc_index_rows s ys x0"
using assms proof (induct ys)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case proof (cases "y = y0")
    case True
    then show ?thesis unfolding calc_index_def by simp
  next
    case False
    then have "y0 \<in> set ys" using Cons.prems by simp
    then show ?thesis using False Cons.hyps by simp
  qed
qed

lemma previous_row_does_not_have_same_variable:
  assumes "y0 \<in> set ys"
  assumes "(x0, k0) \<in> set (post_index_vars (resolve_shuffle m) (seek y0 ys) 
                                           (resolve_shuffle m y0))"
  shows "lookup_row (resolve_shuffle m) x0 k0 ys xs = None"
proof -
  let ?xs0 = "resolve_shuffle m y0"
  have "k0 < calc_index (resolve_shuffle m) (seek y0 ys) ?xs0 x0"
    using assms(2) by (rule give_index_row_position_lt)
  also have "... \<le> calc_index_rows (resolve_shuffle m) ys x0"
    using assms(1) by (rule calc_index_rows_seek)
  finally have "k0 < calc_index_rows (resolve_shuffle m) ys x0" .
  then show ?thesis
    by (rule lookup_row_position_lt_None)
qed

lemma inspect_only_this_row:
  assumes "y0 \<in> set ys"
  assumes "(x0, k0) \<in> set (post_index_vars (resolve_shuffle m) (seek y0 ys)
                                           (resolve_shuffle m y0))"
  shows "lookup_rec m x0 k0 ys
       = lookup_row (resolve_shuffle m) x0 k0 (seek y0 ys) (scan_pair (m y0))"
  using assms 
proof (induct ys)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  show ?case proof (cases "y = y0")
    case True
    then have "\<exists>as. lookup_row (resolve_shuffle m) x0 k0 ys (scan_pair (m y0)) = Some as"
      using Cons by (simp add: there_exists_corresponding_string)
    then show ?thesis using True by auto
  next
    case False
    then have y0: "y0 \<in> set ys" using Cons(2) by simp
    moreover have in_row: "(x0, k0) \<in> set (post_index_vars (resolve_shuffle m) (seek y0 ys) 
                                                           (resolve_shuffle m y0))"
      using Cons(3) False by simp 
    ultimately have *: "lookup_rec m x0 k0 ys = lookup_row (resolve_shuffle m) x0 k0 (seek y0 ys) (scan_pair (m y0))"
      using Cons by simp
    have "lookup_row (resolve_shuffle m) x0 k0 ys (scan_pair (m y)) = None"
      using y0 in_row by (rule previous_row_does_not_have_same_variable)
    then show ?thesis using * False by simp
  qed
qed

lemma lookup_rec_distinct:
  assumes "distinct ys"
  assumes "ys \<noteq> []"
  shows "\<exists>y0 \<in> set ys.
     lookup_rec m x0 k0 ys
   = lookup_row (resolve_shuffle m) x0 k0 (seek y0 ys) (scan_pair (m y0))"
using assms proof (induct ys)
  case Nil
  then show ?case by simp
next
  case (Cons y ys)
  then show ?case proof (cases "ys = []")
    case True
    then show ?thesis by simp
  next
    case False
    then show ?thesis
    proof (cases "lookup_row (resolve_shuffle m) x0 k0 ys (scan_pair (m y))")
      case None
      have "distinct ys" using Cons.prems by simp
      then obtain y0 where
        y0: "y0 \<in> set ys \<and> lookup_rec m x0 k0 ys
                         = lookup_row (resolve_shuffle m) x0 k0 (seek y0 ys) (scan_pair (m y0))"
        using Cons False by blast
      then have y: "y \<noteq> y0" using Cons.prems by auto
      show ?thesis proof (rule bexI)
        show "lookup_rec m x0 k0 (y # ys) 
            = lookup_row (resolve_shuffle m) x0 k0 (seek y0 (y # ys)) (scan_pair (m y0))"
          by (simp add: None y y0)
      next
        show "y0 \<in> set (y # ys)" using y0 by simp
      qed
    next
      case (Some a)
      then show ?thesis by simp
    qed
  qed
qed


lemma all_var_index_less_than:
  fixes s :: "'y shuffle"
  assumes "y0 \<in> set ys"
  assumes "(x0, k0) \<in> set (post_index_vars s (seek y0 ys) (s y0))"
  shows "k0 < calc_index_rows s ys x0"
proof -
  have "k0 < calc_index s (seek y0 ys) (s y0) x0"
    using assms(2)
    by (rule give_index_row_position_lt)
  also have "... \<le> calc_index_rows s ys x0"
    using assms(1) by (rule calc_index_rows_seek)
  finally show ?thesis .
qed

lemma bounded_shuffle_less_than:
  fixes s :: "'y::enum shuffle"
  assumes "bounded_shuffle K s"
  assumes "(x0, k0) \<in> set (post_index_vars s (seek y0 (Enum.enum :: 'y list)) (s y0))"
  shows "k0 < K"
proof -
  let ?enum = "Enum.enum :: 'y list"
  have "y0 \<in> set ?enum"
    by (simp add: enum_UNIV)
  then have "k0 < calc_index_rows s ?enum x0"
    using assms(2) by (rule all_var_index_less_than)
  also have "... = (\<Sum>y::'y\<in>UNIV. count_list (s y) x0)" proof -
    have "distinct ?enum" using enum_distinct by simp
    moreover have "set ?enum = UNIV" using enum_UNIV by simp
    ultimately show ?thesis by (simp add: calc_index_rows_eq_sum)
  qed
  also have "... \<le> K"
    using assms(1) unfolding bounded_shuffle_def by simp
  finally show ?thesis .
qed

lemma bounded_shuffle_var_index_less_than:
  fixes s :: "'y::enum shuffle"
  assumes "bounded_shuffle K s"
  shows "list_all (var_index_less_than K) (give_index_row s (seek y0 (Enum.enum :: 'y list)) (s y0))"
proof (simp only: list_all_iff, rule ballI)
  fix yk
  assume contain: "yk \<in> set (give_index_row s (seek y0 enum_class.enum) (s y0))"
  show "var_index_less_than K yk" proof (auto)
    fix x0 k0
    assume "yk = Inr (x0, Some k0)"
    then have "Inr (x0, Some k0) \<in> set (give_index_row s (seek y0 enum_class.enum) (s y0))"
      using contain by simp
    then show "k0 < K" using bounded_shuffle_less_than[OF assms] by simp
  qed
qed


fun store_resolve_nat :: "('y, 'b) update \<Rightarrow> 'y list \<Rightarrow> ('y + 'y \<times> nat option) \<Rightarrow> ('y + 'b) list" where
  "store_resolve_nat m ys (Inl y) = [Inl y]" |
  "store_resolve_nat m ys (Inr (y, None))   = map Inr (fst (scan (m y)))" |
  "store_resolve_nat m ys (Inr (y, Some n)) = map Inr (lookup m y n ys)"



lemma concat_map_store_resolve_nat:
  fixes B :: "'k::enum boundedness"
  assumes "boundedness B K"
  assumes "list_all (var_index_less_than K) u"
  shows "concat (map (synthesize_store B (resolve_store B m)) (hat_alpha (enum_convert B) u))
       = concat (map (store_resolve_nat m Enum.enum) u)"
using assms(2) proof (induct u rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case by simp
next
  case (Alpha yi xs) 
  then show ?case proof (cases yi rule: index_cases)
    case (VarNone y)
    then show ?thesis using Alpha unfolding resolve_store_def by auto
  next
    case (VarSome y k)
    then have "k < length (Enum.enum :: 'k list)" using Alpha assms(1) unfolding boundedness_def by simp
    then have "enum_to_nat (nat_to_enum k :: 'k) = k" by (rule nat_enum_iso)
    then show ?thesis using Alpha by (auto simp add: VarSome resolve_store_def )
  qed
qed

lemma concat_map_store_resolve_give_index_row:
  fixes B :: "'k::enum boundedness"
  fixes m :: "('y::enum, 'b) update"
  assumes "boundedness B K"
  assumes "bounded K m"
  shows "concat (map (synthesize_store B (resolve_store B m)) (hat_alpha (enum_convert B)
            (give_index_row (resolve_shuffle m) (seek y0 (Enum.enum :: 'y list))
                            (resolve_shuffle m y0))))
       = concat (map (store_resolve_nat m Enum.enum) 
            (give_index_row (resolve_shuffle m) (seek y0 (Enum.enum :: 'y list))
                            (resolve_shuffle m y0)))"
proof -
  have "bounded_shuffle K (resolve_shuffle m)"
    using assms(2) by (rule resolve_bounded)
  then have "list_all (var_index_less_than K) (give_index_row (resolve_shuffle m) (seek y0 (Enum.enum :: 'y list)) ((resolve_shuffle m) y0))"
    by (rule bounded_shuffle_var_index_less_than)
  then show ?thesis
    using assms(1) using concat_map_store_resolve_nat by blast
qed


lemma give_index_row_None:
  assumes "Inr (y, None) \<in> set (give_index_row (resolve_shuffle m) ys xs)"
  shows "y = y0"
using assms by (induct xs, simp_all)


fun store_resolve_row where
  "store_resolve_row s ys as xas (Inl x)           = [Inl x]" |
  "store_resolve_row s ys as xas (Inr (x, None))   = map Inr as" |
  "store_resolve_row s ys as xas (Inr (x, Some k)) =
     map Inr (orNil (lookup_row s x k ys xas))"


lemma store_resolve_only_lookat_one_row:
  fixes m :: "('y::enum, 'b) update"
  fixes y0 :: "'y::enum"
  assumes "y0 \<in> set ys"
  assumes "yk \<in> set (give_index_row (resolve_shuffle m) (seek y0 ys) (resolve_shuffle m y0))"
  shows "store_resolve_nat m ys yk
       = store_resolve_row (resolve_shuffle m) (seek y0 ys) (fst (scan (m y0))) (snd (scan (m y0))) yk"
proof (cases yk)
  case (Inl y)
  then show ?thesis by simp
next
  case (Inr yk)
  then show ?thesis proof (cases yk)
    case (Pair x0 k)
    then show ?thesis proof (cases k)
      case None
      then have "Inr (x0, None) \<in> set (give_index_row (resolve_shuffle m) (seek y0 ys) (resolve_shuffle m y0))"
        using Inr Pair assms by simp
      then have "x0 = y0"
        by (rule give_index_row_None)
      then show ?thesis using assms Inr Pair None by simp
    next
      case (Some k0)
      then have "Inr (x0, Some k0) \<in> set (give_index_row (resolve_shuffle m) (seek y0 ys) (resolve_shuffle m y0))"
        using assms Inr Pair by simp
      then have "lookup_rec m x0 k0 ys
               = lookup_row (resolve_shuffle m) x0 k0 (seek y0 ys) (scan_pair (m y0))"
        using assms by (simp add: inspect_only_this_row)
      then show ?thesis using Inr Pair Some by simp
    qed
  qed
qed


lemma map_store_resolve_nat:
  fixes y0 :: "'y::enum"
  shows "map (store_resolve_nat m Enum.enum) 
             (give_index_row (resolve_shuffle m) (seek y0 Enum.enum) (resolve_shuffle m y0))
       = map (store_resolve_row (resolve_shuffle m) (seek y0 Enum.enum) (fst (scan (m y0))) (snd (scan (m y0))))
             (give_index_row (resolve_shuffle m) (seek y0 Enum.enum) (resolve_shuffle m y0))"
proof -
  have y0: "y0 \<in> set Enum.enum" by (simp add: enum_UNIV)
  show ?thesis
    apply (rule list.map_cong0)
    apply (rule store_resolve_only_lookat_one_row[OF y0])
    apply simp
    done
qed


lemma store_resolve_row_induct_lemma:
  assumes "yk \<in> set (give_index_row s ys (keys_pair xas))"
  shows "store_resolve_row s ys as ((x0, bs) # xas) yk = store_resolve_row s ys as xas yk"
proof (cases yk rule: var_index_cases)
  case (Var y)
  then show ?thesis by simp
next
  case (VarNil y)
  then show ?thesis by simp
next
  case (VarSome y k)
  then show ?thesis proof (cases "y = x0")
    case True
    then show ?thesis using assms by (simp add: VarSome dual_order.strict_implies_not_eq give_index_row_position_lt)
  next
    case False
    then show ?thesis by (simp add: VarSome)
  qed
qed

find_theorems "map ?f ?xs = map ?g ?xs"


lemma concat_map_store_resolve_row_flat_rec:
  "concat (map (store_resolve_row s ys as xas)
            (give_index_row s ys
              (keys_pair xas))) =
         (flat_rec xas)"
proof (induct xas rule: pair_induct)
  case Nil
  then show ?case by (simp)
next
  case (PairCons x bs xas)
  show ?case proof (simp)
    have "concat (map (store_resolve_row s ys as ((x, bs) # xas)) (give_index_row s ys (keys_pair xas)))
        = concat (map (store_resolve_row s ys as xas) (give_index_row s ys (keys_pair xas)))"
      by (rule arg_cong, simp add: store_resolve_row_induct_lemma)
    then show "concat (map (store_resolve_row s ys as ((x, bs) # xas)) (give_index_row s ys (keys_pair xas)))
            = flat_rec xas"
      using PairCons by simp
  qed
qed

lemma resolve_shuffle_keys_pair_scan_pair:
  "resolve_shuffle m x = keys_pair (scan_pair (m x))"
  unfolding resolve_shuffle_def
  by  (simp add: keys_pair_scan_pair)

lemma resolve_store_one_row:
  fixes B :: "'k::enum boundedness"
  fixes m :: "('y::enum, 'b) update"
  assumes "boundedness B k"
  assumes "bounded k m"
  shows "concat (map (synthesize_store B (resolve_store B m))
                  (hat_alpha (enum_convert B) (synthesize_shuffle_nat (resolve_shuffle m) x))) =
         m x"
  apply (simp add: synthesize_shuffle_nat_def concat_map_store_resolve_give_index_row[OF assms])
  apply (simp add: map_store_resolve_nat)
  apply (simp add: resolve_shuffle_keys_pair_scan_pair)
  apply (simp add: concat_map_store_resolve_row_flat_rec resolve_store_def)
  apply (subst scan_pair_def)
  apply (simp only: flat_simp[symmetric])
  apply (simp only: prod.collapse)
  apply (rule scan_inverse)
  done

lemma valuate_concat_map: "valuate (concat (map f xs)) = concat (map valuate (map f xs))"
  by (induct xs, simp_all)

lemma resolve_store_one_row_valuate:
  fixes B :: "'k::enum boundedness"
  fixes m :: "('y::enum, 'b) update"
  assumes "boundedness B k"
  assumes "bounded k m"
  shows "concat (map (resolve_store B m)
                  (valuate (hat_alpha (enum_convert B) (synthesize_shuffle_nat (resolve_shuffle m) x)))) =
         valuate (m x)" (is "?l = ?r")
proof -
  have "?l = valuate (concat (map (synthesize_store B (resolve_store B m))
                     (hat_alpha (enum_convert B) (synthesize_shuffle_nat (resolve_shuffle m) x))))"
  proof -
    fix u
    show "concat (map (resolve_store B m) (valuate u))
      = valuate (concat (map (synthesize_store B (resolve_store B m)) u))"
    proof (induct u rule: xa_induct)
      case Nil
      then show ?case by simp
    next
      case (Var x xs)
      then show ?case by simp
    next
      case (Alpha yk xs)
      then show ?case by (cases yk rule: index_cases, simp_all)
    qed
  qed
  also have "... = ?r"
    using resolve_store_one_row[OF assms] by simp
  finally show ?thesis .
qed

theorem resolve_inverse:
  fixes B :: "'k::enum boundedness"
  fixes m :: "('y::enum, 'b) update"
  assumes "boundedness B k"
  assumes "bounded k m"
  shows "synthesize B (resolve_shuffle m, resolve_store B m) = m"
  by (rule ext, simp add: synthesize_def compU_apply resolve_store_one_row[OF assms])

subsection \<open>Lemmas for counting alphabet\<close>

lemma count_list_resolve_store:
  fixes m :: "('y::enum, 'b) update"
  fixes B :: "'k::enum boundedness"
  fixes a :: "'b"
  assumes "boundedness B k"
  assumes "bounded k m"
  shows "(\<Sum>yk::'y \<times> 'k option\<in>UNIV. count_list (resolve_store B m yk) a)
       = (\<Sum>y::'y \<in>UNIV. count_list (m y) (Inr a))"
  sorry

subsection \<open>Example\<close>

fun poyo :: "(bool, char) update" where
  "poyo False = [Inr (CHR ''A''), Inl True, Inr (CHR ''B''), Inl False, Inr (CHR ''C'')]" |
  "poyo True  = [Inr (CHR ''D''), Inl False, Inr (CHR ''E''), Inl True,  Inr (CHR ''F'')]"

definition testB :: "bool boundedness" where
  "testB = Type_Nat"

lemmas resolve_store_poyo_expand =
  resolve_store_def resolve_shuffle_def
  scan_def scan_pair_def
  enum_to_nat_def calc_index_def
  enum_bool_def

lemma "resolve_store testB poyo (False, None) = ''A''"
  by (simp add: resolve_store_poyo_expand)
  
lemma "resolve_store testB poyo (False, Some False) = ''E''"
  by (simp add: resolve_store_poyo_expand)

lemma "resolve_store testB poyo (False, Some True) = ''C''" 
  by (simp add: resolve_store_poyo_expand)

lemma "resolve_store testB poyo (True, None) = ''D''"
  by (simp add: resolve_store_poyo_expand)

lemma "resolve_store testB poyo (True, Some False) = ''F''"
  by (simp add: resolve_store_poyo_expand)

lemma "resolve_store testB poyo (True, Some True) = ''B''" 
  by (simp add: resolve_store_poyo_expand)


end
