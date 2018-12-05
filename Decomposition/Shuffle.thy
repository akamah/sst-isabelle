(* Title:   Shuffle.thy
   Author:  Akama Hitoshi
*)

theory Shuffle
  imports Main HOL.Enum HOL.List
    "../Util/Enum_Nat" "../Core/Update" "../Single_Use/Single_Use"
begin                                  

subsection \<open>Shuffle\<close>
(* more generic definition of Shuffle *)
type_synonym ('y, 'x) shuffle' = "'y \<Rightarrow> 'x list"

(* Shuffle *)
type_synonym 'y shuffle = "('y, 'y) shuffle'"

definition bounded_shuffle :: "[nat, 'x shuffle] \<Rightarrow> bool" where
  "bounded_shuffle k f \<equiv> \<forall>x. (\<Sum>y\<in>UNIV. count_list (f y) x) \<le> k"

definition resolve_shuffle :: "('y, 'x, 'b) update' \<Rightarrow> ('y, 'x) shuffle'" ("\<pi>\<^sub>1") where
  "resolve_shuffle \<theta> y = extract_variables (\<theta> y)"

lemma sum_specific_if:
  assumes "x0 \<in> A"
  shows "(\<Sum>x::'x::finite\<in>A. if x = x0 then f x else g x)
        = (\<Sum>x\<in>A-{x0}. g x) + f x0" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>x\<in>A-{x0}. if x = x0 then f x else g x) + (\<Sum>x\<in>{x0}. if x = x0 then f x else g x)"
    by (rule sum.subset_diff, simp_all add: assms)
  moreover have "(\<Sum>x\<in>A-{x0}. if x = x0 then f x else g x) = (\<Sum>x\<in>A-{x0}. g x)"
    by (rule sum.cong, auto)
  moreover have "(\<Sum>x\<in>{x0}. if x = x0 then f x else g x) = f x0" by simp
  ultimately show ?thesis by simp
qed

lemma idS_bounded:
  assumes *: "0 < k"
  shows "bounded_shuffle k (idS :: 'y::finite shuffle)"
  unfolding idS_def bounded_shuffle_def
proof (auto)
  fix x :: "'y"
  have "(\<Sum>y\<in>UNIV. if y = x then count_list [] x + 1 else count_list [] x)
      = (count_list [] x + 1) + (\<Sum>y\<in>{x}. count_list [] x)" (is "?lhs = _")
    by (simp add: sum_specific_if)
  also have "... = 1" by simp
  also have "... \<le> k" using * by simp
  finally show "?lhs \<le> k" .
qed

lemma idS_bounded_enum: "bounded_shuffle (length (Enum.enum :: 'k::enum list)) (idS :: 'y::finite shuffle)"
  by (rule idS_bounded) (rule length_enum_gt_0)


lemma count_list_extract_variables: "count_list (extract_variables u) x = count_list u (Inl x)"
  by (induct u rule: xa_induct, simp_all)


lemma resolve_bounded:
  fixes m :: "('x::finite, 'b) update"
  assumes "bounded k m"
  shows "bounded_shuffle k (resolve_shuffle m)"
proof (simp add: bounded_shuffle_def resolve_shuffle_def, rule allI)
  fix x
  show "(\<Sum>y\<in>UNIV. count_list (extract_variables (m y)) x) \<le> k"
    using assms unfolding bounded_def count_var_def
    by (simp add: count_list_extract_variables)
qed

lemma resolve_bounded_inverse:
  fixes m :: "('x::finite, 'b) update"
  assumes "bounded_shuffle k (resolve_shuffle m)"
  shows "bounded k m"
  unfolding bounded_def count_var_def proof (auto)
  fix x
  show "(\<Sum>y\<in>UNIV. count_list (m y) (Inl x)) \<le> k"
    using assms unfolding bounded_shuffle_def resolve_shuffle_def
    by (simp add: count_list_extract_variables)
qed


lemma count_extract_variables:
  fixes m :: "('x::finite, 'a) update"
  shows "(\<Sum>y\<in>(UNIV::'x set). count_list u (Inl y)) = length (extract_variables u)"
proof (induct u rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case proof (simp)
    have "(\<Sum>y\<in>(UNIV::'x set). if x = y then count_list xs (Inl y) + 1 else count_list xs (Inl y))
        = (\<Sum>y\<in>(UNIV::'x set). (if x = y then 1 else 0) + count_list xs (Inl y))" (is "?lhs = _")
    proof (rule sum_cong)
      fix x :: "'x"
      show "x \<in> UNIV" by simp
    next
      show "(\<lambda>y. if x = y then count_list xs (Inl y) + 1  else count_list xs (Inl y)) =
            (\<lambda>y. (if x = y then 1 else 0) + count_list xs (Inl y))"
        by auto
    qed
    also have "...  = (\<Sum>y\<in>(UNIV::'x set). (if x = y then 1 else 0)) + (\<Sum>y\<in>(UNIV::'x set). count_list xs (Inl y))"
      by (rule sum.distrib)
    also have "... = Suc (length (extract_variables xs))" (is "_ = ?rhs")
      by (simp add: Var)
    finally show "?lhs = ?rhs".
  qed
next
  case (Alpha a xs)
  then show ?case by simp
qed


lemma variable_count_in_bounded_shuffle:
  fixes s :: "('x::finite) shuffle"
  assumes "bounded_shuffle k s"
  shows "length (s x0) \<le> card (UNIV::'x set) * k"
proof -
  let ?univ = "UNIV::'x set"
  have *: "\<forall>y. (\<Sum>x\<in>?univ. count_list (s x) y) \<le> k" using assms unfolding bounded_shuffle_def by simp
  have "length (s x0) \<le> (\<Sum>x\<in>?univ. length (s x))" by (rule member_le_sum, simp_all)
  also have "... = (\<Sum>x\<in>?univ. (\<Sum>y\<in>?univ. count_list (s x) y))"
    by (rule sum.cong, simp_all add: sum_count_list_UNIV)
  also have "... = (\<Sum>y\<in>?univ. (\<Sum>x\<in>?univ. count_list (s x) y))"
    by (rule sum.commute)
  also have "... \<le> (\<Sum>y\<in>?univ. k)"
    by (rule sum_mono, simp add: *)
  also have "... = card ?univ * k"
    by simp
  finally show ?thesis .
qed

lemma variable_count_in_bounded_update:
  fixes m :: "('x::finite, 'a) update"
  assumes "bounded k m"
  shows "length (extract_variables (m x0)) \<le> card (UNIV::'x set) * k"
  using assms unfolding bounded_def count_var_def
proof -
  have "bounded_shuffle k (resolve_shuffle m)"
    using assms by (simp add: resolve_bounded)
  then have "length (resolve_shuffle m x0) \<le> card (UNIV::'x set) * k"
    by (simp add: variable_count_in_bounded_shuffle)
  then show ?thesis by (simp add: resolve_shuffle_def)
qed


subsection \<open>Bounded-copy shuffle\<close>

typedef (overloaded) ('e::enum, 'x::finite) bc_shuffle =
  "{m :: 'x shuffle. bounded_shuffle (length (Enum.enum :: 'e list)) m}"
  morphisms Rep_bc_shuffle Abs_bc_shuffle
proof
  show "emptyS \<in> {m :: 'x shuffle. bounded_shuffle (length (Enum.enum :: 'e list)) m}"
    unfolding emptyS_def bounded_shuffle_def by simp
qed


lemma list_length_set_Suc:
  "{xs. length xs = Suc k} = (\<Union>x::'a\<in>UNIV. \<Union>xs\<in>{xs. length xs = k}. { x # xs })" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs" proof (auto, intro exI, auto)
    fix xs :: "'a list"
    show "length xs = Suc k \<Longrightarrow> length (tl xs) = k" by simp
  next
    fix xs :: "'a list"
    show "length xs = Suc k \<Longrightarrow> xs = hd xs # tl xs" by (cases "xs", simp_all)
  qed
next
  show "?rhs \<subseteq> ?lhs" by (auto)
qed

lemma list_length_le_Suc:
  "{xs::'a list. length xs < Suc k} = {xs::'a list. length xs = k} \<union> {xs::'a list. length xs < k}" (is "?lhs = ?rhs")
  by (auto)

lemma finite_list_length_set:
  "finite {xs::'a::finite list. length xs = k}"
  by (induct k, auto simp add: list_length_set_Suc)

lemma finite_list_less_set:
  "finite {xs :: 'a::finite list. length xs < k}"
  by (induct k, auto simp add: list_length_le_Suc finite_list_length_set)

lemma finite_list_le_set:
  "finite {xs :: 'a::finite list. length xs \<le> k}"
proof -
  have "{xs :: 'a::finite list. length xs \<le> k} = {xs::'a list. length xs = k} \<union> {xs::'a list. length xs < k}"
    by auto
  then show ?thesis using finite_list_length_set finite_list_less_set by auto
qed


lemma sum_all_count_list:
  shows "(\<Sum>x::'x::finite\<in>UNIV. count_list xs x) = length xs"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case proof (simp)
    let ?f = "\<lambda>x. if a = x then count_list xs x + 1 else count_list xs x"
    assume assumption: "sum (count_list xs) UNIV = length xs"
    have sum0: "sum ?f (UNIV - {a}) = sum (count_list xs) (UNIV - {a})"
      by (rule sum.cong) auto
    have sum1: "sum ?f {a} = sum (count_list xs) {a} + 1" by simp

    have "sum ?f UNIV = sum ?f (UNIV - {a}) + sum ?f {a}"
      by (rule sum.subset_diff) (simp_all)
    also have "... = sum (count_list xs) (UNIV - {a}) + sum (count_list xs) {a} + 1"
      by (simp only: sum0 sum1)
    also have "... = sum (count_list xs) UNIV + 1"
      apply (simp del: sum.insert)
      apply (rule sum.subset_diff[symmetric], simp_all)
      done
    also have "... = Suc (length xs)" using assumption by simp
    finally show "sum ?f UNIV = Suc (length xs)" .
  qed
qed

lemma
  fixes f :: "'a \<Rightarrow> nat"
  assumes "finite A"
  assumes "y \<in> A"
  shows "f y \<le> sum f A"
  by (simp add: assms(1) assms(2) member_le_sum)
thm member_le_sum


lemma bounded_shuffle_count_list_le_k:
  fixes m :: "'x::finite shuffle"
  assumes "bounded_shuffle k m"
  shows "\<forall>y. count_list (m x) y \<le> k"
proof
  fix y
  have "count_list (m x) y \<le> (\<Sum>z\<in>UNIV. count_list (m z) y)"
    by (rule member_le_sum) (simp_all)
  also have "... \<le> k"
    using assms unfolding bounded_shuffle_def by simp
  finally show "count_list (m x) y \<le> k" .
qed

lemma count_list_le_k_length_card:
  fixes xs :: "'x::finite list"
  assumes "\<forall>x. count_list xs x \<le> k"
  shows "length xs \<le> card (UNIV :: 'x set) * k"
proof -
  have "length xs = (\<Sum>x\<in>UNIV. count_list xs x)"
    by (simp add: sum_all_count_list)
  also have "... \<le> of_nat (card (UNIV :: 'x set)) * k"
    apply (rule sum_bounded_above)
    using assms by simp
  also have "... = card (UNIV :: 'x set) * k" by simp
  finally show ?thesis .
qed

lemma bounded_shuffle_length_card:
  fixes m :: "'x::finite shuffle"
  assumes "bounded_shuffle k m"
  shows "length (m x) \<le> card (UNIV :: 'x set) * k"
  by (simp add: count_list_le_k_length_card bounded_shuffle_count_list_le_k assms)

lemma bounded_shuffle_in_length_set:
  fixes m :: "'x::finite shuffle"
  assumes "bounded_shuffle k m"
  shows "m x \<in> {l::'x list. length l \<le> card (UNIV :: 'x set) * k}"
  using assms by (simp add: bounded_shuffle_length_card)

lemma finite_range_bc_shuffle:
  "finite {y::'x::finite list. \<exists>m::('e::enum, 'x) bc_shuffle. \<exists>x. y = Rep_bc_shuffle m x}" (is "finite ?bcs")
proof -
  have "?bcs \<subseteq> {l::'x list. length l \<le> card (UNIV :: 'x set) * length (Enum.enum :: 'e list)}" (is "_ \<subseteq> ?len")
  proof
    fix l
    assume "l \<in> ?bcs"
    then obtain m :: "('e, 'x) bc_shuffle" and x where l: "l = Rep_bc_shuffle m x" by blast
    then have "bounded_shuffle (length (Enum.enum :: 'e list)) (Rep_bc_shuffle m)" using Rep_bc_shuffle[of "m"]
      by simp
    then show "l \<in> ?len"
      apply (simp only: l)
      apply (rule bounded_shuffle_in_length_set)
      by simp
  qed
  moreover have "finite ?len"
    by (rule finite_list_le_set)
  ultimately show ?thesis
    using infinite_super by auto
qed

(* This proof is heavily inspired by the proof of "instance fun :: finite" *)
instance bc_shuffle :: (enum, finite) finite
proof
  show "finite (UNIV :: ('e::enum, 'x::finite) bc_shuffle set)"
  proof (rule finite_imageD)
    let ?graph = "\<lambda>f :: ('e, 'x) bc_shuffle. {(x, y). y = Rep_bc_shuffle f x}"
    thm finite_imageD
    have "range ?graph \<subseteq> Pow (UNIV \<times> {y::'x::finite list. \<exists>m::('e::enum, 'x) bc_shuffle. \<exists>x. y = Rep_bc_shuffle m x})"
      by (auto)
    moreover have "finite (Pow ((UNIV :: 'x set) \<times> {y::'x::finite list. \<exists>m::('e::enum, 'x) bc_shuffle. \<exists>x. y = Rep_bc_shuffle m x}))"
      by (simp add: finite_range_bc_shuffle)
    ultimately show "finite (range ?graph)"
      by (rule finite_subset)
    show "inj ?graph" proof (rule inj_onI, auto simp add: set_eq_iff)
      fix x y :: "('e, 'x) bc_shuffle"
      assume "\<forall>a b. (b = Rep_bc_shuffle x a) = (b = Rep_bc_shuffle y a)"
      then have "Rep_bc_shuffle x = Rep_bc_shuffle y"
        by auto
      then show "x = y" by (simp add: Rep_bc_shuffle_inject)
    qed
  qed
qed


end
