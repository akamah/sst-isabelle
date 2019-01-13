theory Single_Use
  imports Main "../Util/Setsum" "../Core/Update" "../Core/SST" "../Util/Enum_Nat"
begin


definition kronecker :: "'a \<Rightarrow> 'a \<Rightarrow> nat" where
  "kronecker a b = (if a = b then 1 else 0)"

lemma kronecker_eq[simp]: "kronecker a a = 1" unfolding kronecker_def by simp
lemma kronecker_noteq[simp]: "a \<noteq> b \<Longrightarrow> kronecker a b = 0" unfolding kronecker_def by simp

lemma count_list_my_simp:
  "count_list (x#xs) a = kronecker x a + count_list xs a"
  unfolding kronecker_def by simp

lemma sum_kronecker_in:
  assumes "finite A"
  assumes "b \<in> A"
  shows "(\<Sum>a\<in>A. kronecker b a) = Suc 0"
  by (simp add: sum_eq_Suc0_iff assms kronecker_def)


lemma sum_kronecker_mult1_in:
  assumes "finite A"
  assumes "b \<in> A"
  shows "(\<Sum>a\<in>A. kronecker b a * f a) = f b"
proof -
  have "(\<Sum>a\<in>A. kronecker b a * f a)
       = kronecker b b * f b+ (\<Sum>a\<in>A-{b}. kronecker b a * f a)"
    by (rule sum.remove[OF assms])
  also have "... = f b"
    by (simp add: assms kronecker_def)
  finally show ?thesis .
qed

lemma sum_kronecker_mult2_in:
  assumes "finite A"
  assumes "b \<in> A"
  shows "(\<Sum>a\<in>A. f a * kronecker b a) = f b"
proof -
  have "(\<Sum>a\<in>A. f a * kronecker b a)
       = f b * kronecker b b + (\<Sum>a\<in>A-{b}. f a * kronecker b a)"
    by (rule sum.remove[OF assms])
  also have "... = f b"
    by (simp add: assms kronecker_def)
  finally show ?thesis .
qed

lemma sum_kronecker_notin:
  assumes "finite A"
  assumes "b \<notin> A"
  shows "(\<Sum>a\<in>A. kronecker b a) = 0"
  using assms by (simp add: sum_eq_Suc0_iff assms kronecker_def)

lemma sum_kronecker:
  assumes "finite A"
  shows "(\<Sum>a\<in>A. kronecker b a) \<le> Suc 0"
  using assms
  by (cases "b \<in> A", simp_all add: sum_kronecker_in sum_kronecker_notin)


definition count_var :: "[('x::finite, 'y::finite, 'b) update', 'y] \<Rightarrow> nat" where
  "count_var f y0 \<equiv> \<Sum>y\<in>UNIV. count_list (extract_variables (f y)) y0"

definition count_alpha :: "[('x::finite, 'y::finite, 'b) update', 'b] \<Rightarrow> nat" where
  "count_alpha f b0 \<equiv> \<Sum>y\<in>UNIV. count_list (valuate (f y)) b0"

lemma count_list_extract_variables: "count_list (extract_variables u) x = count_list u (Inl x)"
  by (induct u rule: xa_induct, simp_all)

lemma count_list_valuate: "count_list (valuate u) a = count_list u (Inr a)"
  by (induct u rule: xa_induct, simp_all)


lemma sum_count_list_UNIV: "(\<Sum>y\<in>(UNIV::'x::finite set). count_list xs y) = length xs"
  by (rule sum_count_set, simp_all)


definition bounded :: "[nat, ('x::finite, 'y::finite, 'b) update'] \<Rightarrow> bool" where
  "bounded k f \<equiv> (\<forall>y. count_var f y \<le> k)"

abbreviation single_use  :: "(('x::finite, 'y::finite, 'b) update') \<Rightarrow> bool" where
  "single_use f \<equiv> bounded 1 f"

lemma count_list_append[simp]: "count_list (xs@ys) a = count_list xs a + count_list ys a"
  by (induct xs, auto)

lemma card_UNIV_option: "card (UNIV::('a::finite) option set) = Suc (card (UNIV::'a set))"
  by (auto simp add: UNIV_option_conv, rule card_image, rule inj_Some)

lemma basic_count: "count_list (extract_variables (hat_hom f u)) y
  = (\<Sum>z\<in>(UNIV::('a::finite) set). (count_list (extract_variables (f z)) y * count_list (extract_variables u) z))"
proof (induct u rule: xa_induct)
  case Nil
  show ?case by simp
next
  case (Alpha a u) 
  then show ?case by simp
next
  case (Var x u)
  then show ?case by (simp add: count_list_my_simp add_mult_distrib2 sum.distrib sum_kronecker_mult2_in del: count_list.simps)
qed

lemma count_var_comp:
  fixes m1 :: "('y::finite, 'z::finite, 'b) update'"
  fixes m2 :: "('x::finite, 'y, 'b) update'"
  shows "count_var (m1 \<bullet> m2) x
       = (\<Sum>y::'y\<in>UNIV. count_list (extract_variables (m1 y)) x * count_var m2 y)"
  unfolding compU_def count_alpha_def count_var_def
  by (simp add: basic_count sum_distrib_left, rule sum.commute)


lemma bounded_copy_closed:
  fixes f :: "('y::finite, 'z::finite, 'b) update'"
  assumes "bounded k f" and "bounded l g"
  shows "bounded (k * l) (f \<bullet> g)"
  unfolding bounded_def
proof (simp add: count_var_comp, rule allI)
  fix y
  have "(\<Sum>ya\<in>UNIV. count_list (extract_variables (f ya)) y * count_var g ya)
      \<le> (\<Sum>ya\<in>UNIV. count_list (extract_variables (f ya)) y * l)" (is "?def \<le> _")
    apply (rule sum_mono, rule mult_le_mono2)
    using assms unfolding bounded_def by simp
  also have "... \<le> k * l"
    using assms unfolding bounded_def count_var_def
    by (simp add: sum_distrib_right[symmetric])
  finally show "?def \<le> k * l" .
qed

lemma single_use_closed:
  fixes f :: "('y::finite, 'z::finite, 'b) update'"
  assumes "single_use f" and "single_use g"
  shows "single_use (f \<bullet> g)"
  using bounded_copy_closed[OF assms] by simp


lemma basic_count_alpha:
  fixes m :: "('y::finite, 'z::finite, 'b) update'"
  fixes xs :: "('y + 'b) list"
  shows "count_list (valuate (hat_hom m u)) a =
         (\<Sum>y::'y\<in>UNIV. (count_list (valuate (m y)) a * count_list (extract_variables u) y)) + count_list (valuate u) a"
proof (induct u rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case by (simp del: count_list.simps add: count_list_my_simp add_mult_distrib2 sum.distrib sum_kronecker_mult2_in)
next
  case (Alpha a xs)
  then show ?case by simp
qed


lemma count_alpha_comp:
  fixes m1 :: "('y::finite, 'z::finite, 'b) update'"
  fixes m2 :: "('x::finite, 'y, 'b) update'"
  shows "count_alpha (m1 \<bullet> m2) a
 = (\<Sum>y::'y\<in>UNIV. count_list (valuate (m1 y)) a * count_var m2 y) + count_alpha m2 a"
  unfolding compU_def count_alpha_def count_var_def
  by (simp add: basic_count_alpha sum_distrib_right sum_distrib_left sum.distrib, rule sum.commute)

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
  then have 1: "(\<Sum>y\<in>UNIV. count_list (valuate (m1 y)) a) = 1" unfolding count_alpha_def by simp
  obtain y1 where y1: "count_list (valuate (m1 y1)) a = 1 \<and> (\<Sum>y0\<in>UNIV-{y1}. count_list (valuate (m1 y0)) a) = 0"
    using sum1[OF finite 1] by auto
  then have y0: "\<forall>y0\<in>UNIV-{y1}. count_list (valuate (m1 y0)) a = 0" by auto
  have "(\<Sum>y\<in>UNIV. count_list (valuate (m1 y)) a * count_var m2 y) = (\<Sum>y\<in>UNIV. if y = y1 then count_var m2 y else 0)"
    by (rule sum.cong, auto simp add: y0 y1)
  also have "... = count_var m2 y1" by simp
  finally have *: "(\<Sum>y\<in>UNIV. count_list (valuate (m1 y)) a  * count_var m2 y) = count_var m2 y1" .
  have "(\<Sum>y\<in>UNIV. count_list (valuate (m1 y)) a * count_var m2 y) \<le> k"
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
datatype ('i::enum) boundedness = Boundedness

definition boundedness :: "'i::enum boundedness \<Rightarrow> nat \<Rightarrow> bool" where 
  "boundedness B k \<equiv> (k = length (Enum.enum :: 'i list))"

end
