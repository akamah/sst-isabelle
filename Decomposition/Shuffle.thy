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

lemma finite_list_le_set:
  "finite {xs :: 'a::finite list. length xs < k}"
  by (induct k, auto simp add: list_length_le_Suc finite_list_length_set)


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


lemma 
  fixes m :: "'x shuffle"
  assumes "bounded_shuffle k m"
  shows "m x \<in> {l::'x list. length l \<le> card (UNIV :: 'x set) * k}"
  using assms unfolding bounded_shuffle_def proof (simp)

lemma "finite {l. \<exists>m x. bounded_shuffle k m \<and> l = m x}"
  thm Rep_bc_shuffle
  apply (auto simp add: sum_all_count_list)
  oops


(* This proof is heavily inspired by the proof of "instance fun :: finite" *)
instance bc_shuffle :: (enum, finite) finite
proof
  show "finite (UNIV :: ('e::enum, 'x::finite) bc_shuffle set)"
  proof (rule finite_imageD)
    let ?graph = "\<lambda>f :: ('e, 'x) bc_shuffle. {(x, y). y = Rep_bc_shuffle f x}"
    thm finite_imageD
    have "range ?graph \<subseteq> Pow UNIV"
      by simp
    show "finite (range ?graph)" sorry thm finite_Pow_iff
    show "inj ?graph" proof (rule inj_onI, auto simp add: set_eq_iff)
      fix x y :: "('e, 'x) bc_shuffle"
      assume "\<forall>a b. (b = Rep_bc_shuffle x a) = (b = Rep_bc_shuffle y a)"
      then have "Rep_bc_shuffle x = Rep_bc_shuffle y"
        by blast
      then show "x = y" by (simp add: Rep_bc_shuffle_inject)
    qed
  qed
qed


end
