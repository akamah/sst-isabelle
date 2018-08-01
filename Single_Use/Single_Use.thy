theory Single_Use
  imports Main "../Util/Setsum" "../Core/Update" "../Decomposition/Decompose_Update"
begin

lemma sum_cong: "\<And>x. x\<in>A \<Longrightarrow> f = g \<Longrightarrow> sum f A = sum g A" by auto

definition count_var :: "[('x::finite, 'y::finite, 'b) update', 'y] \<Rightarrow> nat" where
  "count_var f y0 \<equiv> \<Sum>y\<in>UNIV. count_list (f y) (Inl y0)"

lemma "count_list (f y) (Inl x) \<le> count_var f x"
proof -
  have "(\<Sum>y\<in>UNIV. count_list (f y) (Inl x))
      = (\<Sum>y\<in>(UNIV -{y}). count_list (f y) (Inl x)) + (\<lambda>y. count_list (f y) (Inl x)) y"
    by (simp add: add.commute sum.remove)
  thus ?thesis
    by (simp add: count_var_def)
qed

definition bounded :: "[nat, ('x::finite, 'y::finite, 'b) update'] \<Rightarrow> bool" where
  "bounded k f \<equiv> (\<forall>y. count_var f y \<le> k)"

definition bounded_shuffle :: "[nat, 'x shuffle] \<Rightarrow> bool" where
  "bounded_shuffle k f \<equiv> \<forall>x. (\<Sum>y\<in>UNIV. count_list (f y) x) \<le> k"

lemma resolve_bounded:
  fixes m :: "('x::finite, 'b) update"
  assumes "bounded k m"
  shows "bounded_shuffle k (resolve_shuffle m)"
proof (simp add: bounded_shuffle_def resolve_shuffle_def, rule allI)
  fix x
  { fix x' :: 'x and u :: "('x + 'b) list"
    have "count_list (extract_variables u) x' = count_list u (Inl x')"
      by (induct u rule: xa_induct, simp_all)
  } note that = this
  then show "(\<Sum>y\<in>UNIV. count_list (extract_variables (m y)) x) \<le> k"
    using assms unfolding bounded_def count_var_def
    by simp
qed

abbreviation single_use  :: "(('x::finite, 'y::finite, 'b) update') \<Rightarrow> bool" where
  "single_use f \<equiv> bounded 1 f"

lemma [simp]:  "count_list (xs@ys) a = count_list xs a + count_list ys a"
  by (induct xs, auto)



lemma basic_count: "count_list (hat_hom f xs) (Inl y) =
                    (\<Sum>z\<in>(UNIV::('a::finite) set). (count_list (f z) (Inl y) * count_list xs (Inl z)))"
proof (induct xs rule: xa_induct)
  case Nil
  show ?case by simp
next
  case (Alpha a xs) 
  then show ?case by simp
next
  case (Var x xs)
  then show ?case proof (simp)
    have "(\<Sum>z\<in>UNIV. count_list (f z) (Inl y) * (if x = z then count_list xs (Inl z) + 1 
                                                          else count_list xs (Inl z)))
        = (\<Sum>z\<in>UNIV. count_list (f z) (Inl y) * count_list xs (Inl z) 
                   + (if x = z then count_list (f z) (Inl y) else 0))"
      by (rule sum_cong, auto)
    also have "... = (\<Sum>z\<in>UNIV. count_list (f z) (Inl y) * count_list xs (Inl z))
                      + (\<Sum>z\<in>UNIV. if x = z then count_list (f z) (Inl y) else 0)"
      by (rule sum.distrib)
    finally have "(\<Sum>z\<in>UNIV. count_list (f z) (Inl y) * (if x = z then count_list xs (Inl z) + 1 
                                                                  else count_list xs (Inl z)))
                 = (\<Sum>z\<in>UNIV. count_list (f z) (Inl y) * count_list xs (Inl z))
                    + (\<Sum>z\<in>UNIV. if x = z then count_list (f z) (Inl y) else 0)" .
    then show "count_list (f x) (Inl y) + (\<Sum>z\<in>UNIV. count_list (f z) (Inl y) * count_list xs (Inl z)) 
            = (\<Sum>z\<in>UNIV. count_list (f z) (Inl y) * (if x = z then count_list xs (Inl z) + 1 
                                                              else count_list xs (Inl z)))"
      by simp
  qed
qed


lemma
  fixes f :: "('y::finite, 'z::finite, 'b) update'"
  assumes "single_use f" and "single_use g"
  shows "single_use (f \<bullet> g)"
  unfolding bounded_def
proof (rule allI)
  have[rule_format, simp]: "\<forall>x y. count_list (g y) (Inl x) \<le> Suc 0"
  proof (intro allI)
    fix x y
    show "count_list (g y) (Inl x) \<le> Suc 0"
    proof (rule sumk[of UNIV y], auto)
      from assms
      have "count_var g x \<le> Suc 0"
        by (simp add: bounded_def)
      thus "(\<Sum>a\<in>UNIV. count_list (g a) (Inl x)) \<le> Suc 0"
        by (simp add: count_var_def)
    qed
  qed
  fix x :: "'z"
  show "count_var (f \<bullet> g) x \<le> 1"
  proof (auto simp add: count_var_def)
    from assms
    have "count_var f x \<le> Suc 0"
      by (simp add:  bounded_def)
    hence "count_var f x = 0 \<or> count_var f x = 1"
      by auto
    thus "(\<Sum>y\<in>UNIV. count_list ((f \<bullet> g) y) (Inl x)) \<le> Suc 0"
    proof
      assume "count_var f x = 0"
      hence [simp]: "\<forall>y. count_list (f y) (Inl x) = 0"
        unfolding count_var_def
        by (auto)
      show ?thesis
        by (simp add: basic_count comp_def)
    next
      assume a1: "count_var f x = 1"
      show ?thesis
      proof (simp add: comp_def basic_count)
        have "\<exists>y \<in> UNIV. (\<lambda>y. count_list (f y) (Inl x)) y = 1 \<and> sum (\<lambda>y. count_list (f y) (Inl x)) (UNIV - {y}) = 0"
          by (rule sum1, simp, insert a1, simp add: count_var_def)
        then obtain z where z: "(\<lambda>y. count_list (f y) (Inl x)) z = Suc 0"
          "sum (\<lambda>y. count_list (f y) (Inl x)) (UNIV - {z}) = 0"
          by auto
        have "(\<Sum>y\<in>UNIV. \<Sum>b\<in>UNIV. count_list (f b) (Inl x) * count_list (g y) (Inl b))
            \<le> (\<Sum>y\<in>UNIV. count_list (g y) (Inl z))"
        proof (rule sum_mono)
          fix y
          have "(\<Sum>b\<in>UNIV. count_list (f b) (Inl x) * count_list (g y) (Inl b)) =
                (\<Sum>b\<in>(insert z (UNIV - {z})). count_list (f b) (Inl x) * count_list (g y) (Inl b))"
            by (simp add: insert_UNIV)
          also have "... = count_list (f z) (Inl x) * count_list (g y) (Inl z) +
             (\<Sum>b\<in>(UNIV - {z}). count_list (f b) (Inl x) * count_list (g y) (Inl b))"
            by (rule sum.insert, auto)
          also have "... =  count_list (g y) (Inl z)"
            using z by (simp)
          finally show "(\<Sum>b\<in>UNIV. count_list (f b) (Inl x) * count_list (g y) (Inl b)) \<le>
            count_list (g y) (Inl z)"
            by simp
        qed
        also have "... \<le> Suc 0"
          using assms by (simp add: bounded_def count_var_def)
        finally show "(\<Sum>y\<in>UNIV. \<Sum>b\<in>UNIV. count_list (f b) (Inl x) * count_list (g y) (Inl b)) \<le> Suc 0"
          by simp
      qed
    qed
  qed
qed

end
