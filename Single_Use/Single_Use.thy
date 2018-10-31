theory Single_Use
  imports Main "../Util/Setsum" "../Core/Update" "../Core/SST" "../Util/Enum_Nat"
begin

lemma sum_cong: "\<And>x. x\<in>A \<Longrightarrow> f = g \<Longrightarrow> sum f A = sum g A" by auto

definition count_var :: "[('x::finite, 'y::finite, 'b) update', 'y] \<Rightarrow> nat" where
  "count_var f y0 \<equiv> \<Sum>y\<in>UNIV. count_list (f y) (Inl y0)"

definition count_alpha :: "[('x::finite, 'y::finite, 'b) update', 'b] \<Rightarrow> nat" where
  "count_alpha f b0 \<equiv> \<Sum>y\<in>UNIV. count_list (f y) (Inr b0)"

lemma "count_list (f y) (Inl x) \<le> count_var f x"
proof -
  have "(\<Sum>y\<in>UNIV. count_list (f y) (Inl x))
      = (\<Sum>y\<in>(UNIV -{y}). count_list (f y) (Inl x)) + (\<lambda>y. count_list (f y) (Inl x)) y"
    by (simp add: add.commute sum.remove)
  thus ?thesis
    by (simp add: count_var_def)
qed


lemma count_list_map_inj:
  assumes "inj f"
  shows "count_list (map f w) (f a) = count_list w a"
proof (induct w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case using assms by (simp add: injD)
qed

lemma count_list_Inr:
  "count_list (map Inr w) (Inr a) = count_list w a"
  by (simp add: count_list_map_inj)


lemma sum_count_list_inj:
  fixes f :: "'y::finite \<Rightarrow> 'z"
  assumes "inj f"
  shows "(\<Sum>ya\<in>UNIV. count_list [f ya] (f y)) = 1"
proof -
  have f_ya: "\<forall>ya. [f ya] = map f [ya]" by simp
  show ?thesis
    apply (simp only: f_ya count_list_map_inj[OF assms])
    apply simp
    apply (simp only: count_list.simps(1))
    apply simp
    done
qed

lemma sum_count_list_UNIV: "(\<Sum>y\<in>(UNIV::'x::finite set). count_list xs y) = length xs"
  by (rule sum_count_set, simp_all)


definition bounded :: "[nat, ('x::finite, 'y::finite, 'b) update'] \<Rightarrow> bool" where
  "bounded k f \<equiv> (\<forall>y. count_var f y \<le> k)"

abbreviation single_use  :: "(('x::finite, 'y::finite, 'b) update') \<Rightarrow> bool" where
  "single_use f \<equiv> bounded 1 f"

lemma [simp]:  "count_list (xs@ys) a = count_list xs a + count_list ys a"
  by (induct xs, auto)

lemma card_UNIV_option: "card (UNIV::('a::finite) option set) = Suc (card (UNIV::'a set))"
  by (auto simp add: UNIV_option_conv, rule card_image, rule inj_Some)

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
        by (simp add: basic_count compU_apply)
    next
      assume a1: "count_var f x = 1"
      show ?thesis
      proof (simp add: compU_apply basic_count)
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

lemma basic_count_alpha:
  fixes m :: "('y::finite, 'z::finite, 'b) update'"
  fixes xs :: "('y + 'b) list"
  shows "count_list (hat_hom m xs) (Inr a) =
         (\<Sum>y::'y\<in>UNIV. (count_list (m y) (Inr a) * count_list xs (Inl y))) + count_list xs (Inr a)"
proof (induct xs rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case proof (simp)
    let ?f = "\<lambda>y. count_list (m y) (Inr a) * count_list xs (Inl y)"
    let ?g = "\<lambda>y. count_list (m y) (Inr a) * (if x = y then count_list xs (Inl y) + 1 else count_list xs (Inl y))"
    let ?h = "\<lambda>y. count_list (m y) (Inr a) * count_list xs (Inl y) + (if x = y then count_list (m y) (Inr a) else 0)"
    let ?l = "count_list (m x) (Inr a)"

    have "sum ?g UNIV = sum ?h UNIV"
      by (rule sum.cong, auto)
    also have "... = sum ?f UNIV + ?l"
      by (simp add: sum.distrib)
    finally have "sum ?g UNIV = sum ?f UNIV + ?l".
    then show "?l + sum ?f UNIV = sum ?g UNIV" by simp
  qed
next
  case (Alpha a xs)
  then show ?case by simp
qed


lemma count_alpha_comp:
  fixes m1 :: "('y::finite, 'z::finite, 'b) update'"
  fixes m2 :: "('x::finite, 'y, 'b) update'"
  shows "count_alpha (m1 \<bullet> m2) a
 = (\<Sum>y::'y\<in>UNIV. count_list (m1 y) (Inr a) * count_var m2 y) + count_alpha m2 a"
  unfolding compU_def count_alpha_def count_var_def
proof (simp)
  have "(\<Sum>y\<in>UNIV. count_list (m1 y) (Inr a) * (\<Sum>x\<in>UNIV. count_list (m2 x) (Inl y)))
      = (\<Sum>y\<in>UNIV. \<Sum>x\<in>UNIV. count_list (m1 y) (Inr a) * count_list (m2 x) (Inl y))" (is "?lhs = _")
    by (simp add: sum_distrib_left)
  also have "... = (\<Sum>x\<in>UNIV. \<Sum>y\<in>UNIV. count_list (m1 y) (Inr a) * count_list (m2 x) (Inl y))" (is "_ = ?rhs")
    by (rule sum.commute)
  finally have "?lhs = ?rhs" .

  then show "(\<Sum>x\<in>UNIV. count_list (hat_hom m1 (m2 x)) (Inr a)) =
             (\<Sum>y\<in>UNIV. count_list (m1 y) (Inr a) * (\<Sum>x\<in>UNIV. count_list (m2 x) (Inl y))) +
             (\<Sum>x\<in>UNIV. count_list (m2 x) (Inr a))"
    by (simp add: basic_count_alpha sum.distrib)
qed  


lemma count_alpha_0_comp_count_alpha_n:
  assumes "count_alpha m1 a = 0"
  assumes "count_alpha m2 a \<le> n"
  shows "count_alpha (m1 \<bullet> m2) a \<le> n"
  using assms by (simp add: count_alpha_comp, simp add: count_alpha_def)


lemma count_alpha_le_1_bounded_copy:
  assumes "count_alpha m1 a \<le> 1"
  assumes "count_alpha m2 a \<le> n"
  assumes "bounded k m2"
  shows "count_alpha (m1 \<bullet> m2) a \<le> k + n"
proof (cases "count_alpha m1 a = 0")
  case True
  then show ?thesis using assms by (simp add: count_alpha_comp, simp add: count_alpha_def)
next
  case False
  then have "count_alpha m1 a = 1" using assms(1) by simp
  then have 1: "(\<Sum>y\<in>UNIV. count_list (m1 y) (Inr a)) = 1" unfolding count_alpha_def by simp
  obtain y1 where y1: "count_list (m1 y1) (Inr a) = 1 \<and> (\<Sum>y0\<in>UNIV-{y1}. count_list (m1 y0) (Inr a)) = 0"
    using sum1[OF finite 1] by auto
  then have y0: "\<forall>y0\<in>UNIV-{y1}. count_list (m1 y0) (Inr a) = 0" by auto
  have "(\<Sum>y\<in>UNIV. count_list (m1 y) (Inr a) * count_var m2 y) = (\<Sum>y\<in>UNIV. if y = y1 then count_var m2 y else 0)"
    by (rule sum.cong, auto simp add: y0 y1)
  also have "... = count_var m2 y1" by simp
  finally have *: "(\<Sum>y\<in>UNIV. count_list (m1 y) (Inr a) * count_var m2 y) = count_var m2 y1" .
  have "(\<Sum>y\<in>UNIV. count_list (m1 y) (Inr a) * count_var m2 y) \<le> k"
    using assms unfolding bounded_def by (simp add: "*")
  then show ?thesis using assms unfolding bounded_def
    by (simp add: count_alpha_comp)
qed


section \<open>Bounded-ness of SST\<close>

definition bounded_copy_SST :: "[ nat, ('q::finite, 'x::finite, 'a, 'b, 'e) SST_scheme ] \<Rightarrow> bool" where
  "bounded_copy_SST k sst \<equiv> (\<forall>w q. reachable sst q \<longrightarrow> bounded k (SST.eta_hat sst (q, w)))"

lemma bounded_copy_SST_simp:
  assumes "bounded_copy_SST k sst" and "reachable sst q"
  shows "bounded k (SST.eta_hat sst (q, w))"
  using assms unfolding bounded_copy_SST_def by simp

text \<open>Phantom type used to state bounded-ness using size of UNIV :: 'i set\<close>
type_synonym 'i boundedness = "'i type_nat"

definition boundedness :: "'i::enum boundedness \<Rightarrow> nat \<Rightarrow> bool" where 
  "boundedness B k \<equiv> (k = length (Enum.enum :: 'i list))"

end
