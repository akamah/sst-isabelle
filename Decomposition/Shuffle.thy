theory Shuffle
  imports Main Enum List "../Util/Enum_Nat" "../Core/Update" "../Single_Use/Single_Use" "Decompose_Update"
begin                                  


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
