(* Title:   Setsum.thy
   Author:  Minamide Yasuhiko
*)

theory Setsum
  imports Main
begin


lemma sum1:
  fixes f::"'a \<Rightarrow> nat"
  assumes "finite s" "sum f s = 1"
  shows "\<exists>y \<in> s. f y = 1 \<and> sum f (s - {y}) = 0"
  using assms apply (simp add: sum_eq_1_iff[OF assms(1), simplified]) by fastforce

lemma sumk:
  fixes f::"'a \<Rightarrow> nat"
  assumes "finite s" "x \<in> s" "sum f s \<le> k"
  shows "f x \<le> k"
proof (rule contrapos_pp)
  assume H: "\<not> f x \<le> k"
  have "sum f s = sum f (insert x (s - {x}))"
    using assms by (simp add: insert_absorb)
  also have "... = f x + sum f (s - {x})"
    by (rule sum.insert, insert assms, auto)
  finally have "sum f s = f x + sum f (s - {x})" .
  thus "\<not> sum f s \<le> k"
  proof (simp)
    show "\<not> f x + sum f (s - {x}) \<le> k"
      using H by auto
  qed
qed (fact)


end
