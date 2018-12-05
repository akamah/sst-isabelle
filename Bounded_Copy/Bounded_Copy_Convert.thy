theory Bounded_Copy_Convert
  imports Main HOL.Finite_Set
          "../Util/Enum_Nat" "../Core/Update" "../Single_Use/Single_Use" "../Decomposition/Decompose_Update"
          "../Composition/Convert_Monoid_SST" "../Type/Monoid_SST_Type"
begin


lemma "count_alpha (synthesize_shuffle_nat s) yk
     = undefined"
proof (cases yk rule: index_cases)
  case (VarNone y)
  then show ?thesis unfolding count_alpha_def synthesize_shuffle_nat_def
    

next
  case (VarSome y k)
  then show ?thesis sorry
qed




lemma count_alpha_iota_le_1:
  fixes \<alpha> :: "'x \<Rightarrow> 'y::enum shuffle"
  assumes "boundedness (B :: 'k::enum boundedness) k"
  assumes "bounded_shuffle k (\<alpha> x)"
  shows "count_alpha (\<iota> B \<alpha> x :: ('y, 'x \<times> ('y, 'k::enum) index + 'b) update) (Inl (x0, y0, z0) :: 'x \<times> ('y, 'k::enum) index + 'b) \<le> 1"
  unfolding \<iota>_def

lemma count_alpha_iota_x_neq_x0_eq_0:
  fixes \<alpha> :: "'x \<Rightarrow> 'y::enum shuffle"
  assumes "x \<noteq> x0"
  assumes "boundedness (B :: 'k::enum boundedness) k"
  assumes "bounded_shuffle k (\<alpha> x)"
  shows "count_alpha (\<iota> B \<alpha> x :: ('y, 'x \<times> ('y, 'k::enum) index + 'b) update) (Inl (x0, y0, z0) :: 'x \<times> ('y, 'k::enum) index + 'b) = 0"
proof -
  have w: "\<forall>yi\<in>set (\<iota> B \<alpha> x y0). pred_only_x_y x y0 yi"
    by (simp add: iota_x_y Ball_set_list_all)
  have "\<forall>y. count_list (\<iota> B \<alpha> x y) (Inr (Inl (x0, y0, z0))) = 0"
    by (metis assms(1) count_notin pred_only_x_y_apply w y_neq_y0_count_list_zero)
  then show ?thesis unfolding count_alpha_def
    by simp
qed

lemma count_list_inr_list_Inl: "count_list (hat_alpha inr_list w) (Inr (Inl xyz)) = 0"
  by (induct w rule: xa_induct, simp_all)

lemma count_alpha_inr_list: "count_alpha (inr_list \<star> a) (Inl xyz) = 0"
  unfolding count_alpha_def map_alpha_def by (simp add: count_list_inr_list_Inl)

lemma count_alpha_hat_homU_eta_hat:
  fixes msst :: "('q::finite, 'x::finite, 'y::enum, 'a, 'b) MSST"
  fixes B1 :: "'k::enum boundedness"
  fixes B2 :: "'l::enum boundedness"
  assumes bc_msst: "bounded_copy_SST k msst"
  assumes boundedness_l: "boundedness B2 l"
  assumes typed: "is_type msst \<gamma>"
  assumes bc_type: "bounded_copy_type l msst \<gamma>"
  assumes reach: "reachable (convert_MSST B2 msst) (q1, \<beta>)"
  assumes tail: "u \<in> tails (SST.eta_hat msst (q1, w) x)"
  shows "count_alpha (hat_homU (\<iota> B2 (Rep_alpha B2 \<beta>)) u) (Inl (x0, y0, z0))
       \<le> count_list u (Inl x0) * l"
using tail proof (induct u rule: xa_induct)
case Nil
  then show ?case by (simp add: idU_def count_alpha_def)
next
  case (Var x' xs)
  then show ?case proof -
    have xs: "xs \<in> tails (SST.eta_hat msst (q1, w) x)" proof -
      thm tails_def
      obtain ys where "ys @ Inl x' # xs = SST.eta_hat msst (q1, w) x"
        using Var.prems unfolding tails_def by auto
      then have body: "SST.eta_hat msst (q1, w) x = (ys @ [Inl x']) @ xs" by simp
      show ?thesis unfolding tails_def by (simp, rule exI[where x="ys @ [Inl x']"], rule body)
    qed
    note IH = Var.hyps(1)[OF xs]
    have rep: "Rep_alpha B2 \<beta> x' \<in> \<gamma> (q1, x')"
      by (rule condition_of_convert_MSST_reachable_state[OF boundedness_l typed bc_type reach])
    then have bs: "bounded_shuffle l (Rep_alpha B2 \<beta> x')"
      using bc_type unfolding bounded_copy_type_def
      by (meson reach reachable_convert)
    note bc = hat_homU_iota_bounded_copy_tail[OF boundedness_l typed bc_type reach xs]
    show ?thesis proof (cases "x' = x0")
      case True
      then show ?thesis proof -
        have x: "count_alpha (\<iota> B2 (Rep_alpha B2 \<beta>) x0) (Inl (x0, y0, z0)) \<le> 1"
          apply (rule count_alpha_iota_le_1[OF boundedness_l])
          using bs by (simp add: True)
        show ?thesis by (simp del: Rep_alpha.simps add: True count_alpha_le_1_bounded_copy[OF x IH bc])
      qed
    next
      case False
      then show ?thesis proof -
        have x: "count_alpha (\<iota> B2 (Rep_alpha B2 \<beta>) x') (Inl (x0, y0, z0)) = 0"
          apply (rule count_alpha_iota_x_neq_x0_eq_0[OF False boundedness_l])
          using bs by simp
        show ?thesis by (simp del: Rep_alpha.simps add: False count_alpha_0_comp_count_alpha_n[OF x IH])
      qed
    qed
  qed
next
  case (Alpha a xs)
  then show ?case proof -
    have xs: "xs \<in> tails (SST.eta_hat msst (q1, w) x)" proof -
      thm tails_def
      obtain ys where "ys @ Inr a # xs = SST.eta_hat msst (q1, w) x"
        using Alpha.prems unfolding tails_def by auto
      then have body: "SST.eta_hat msst (q1, w) x = (ys @ [Inr a]) @ xs" by simp
      show ?thesis unfolding tails_def by (simp, rule exI[where x="ys @ [Inr a]"], rule body)
    qed
    note IH = Alpha.hyps(1)[OF xs]
    have a: "count_alpha (inr_list \<star> a) (Inl (x0, y0, z0)) = 0" by (simp add: count_alpha_inr_list)
    show ?thesis by (simp del: Rep_alpha.simps add: count_alpha_0_comp_count_alpha_n[OF a IH ])
  qed
qed




definition iterate_range :: "'k::enum boundedness \<Rightarrow> ('y::enum \<times> nat option) set"  where
  "iterate_range B = range (to_nat B)"

lemma iterate_range_finite[simp]:
  "finite (iterate_range B)"
  unfolding iterate_range_def by simp

lemma iterate_range_None[simp]:
  "(y::'y::enum, None) \<in> iterate_range (B :: 'k::enum boundedness)"
proof -
  have "(y, None :: 'k option) \<in> UNIV" by simp
  moreover have "(y, None) = to_nat B (y, None)" by simp
  ultimately show ?thesis unfolding iterate_range_def by blast
qed

lemma iterate_range_Some[simp]:
  fixes B :: "'k::enum boundedness"
  assumes "boundedness B K"
  assumes "k < K"
  shows "(y::'y::enum, Some k) \<in> iterate_range B"
proof -
  have "(y, Some (nat_to_enum k :: 'k)) \<in> UNIV" by simp
  moreover have "(y, Some k) = to_nat B (y, Some (nat_to_enum k :: 'k))"
    using assms unfolding boundedness_def by (simp add: nat_enum_iso)
  ultimately show ?thesis unfolding iterate_range_def by blast
qed


lemma inj_to_nat:
  "inj (to_nat B :: 'y::enum \<times> 'k::enum option \<Rightarrow> 'y \<times> nat option)"
  unfolding inj_on_def
proof (auto)
  fix x0 k0 x1 k1
  assume "to_nat B (x0 :: 'y, k0) = to_nat B (x1 :: 'y, k1)"
  then have *: "x0 = x1 \<and> k0 = k1"
    using inj_enum_to_nat by (cases k0; cases k1, auto simp add: inj_on_def)
  show "x0 = x1" using * by simp
  show "k0 = k1" using * by simp
qed

lemma sum_decompose_to_nat:
  fixes m :: "('y::enum, 'b) update"
  fixes B :: "'k::enum boundedness"
  shows "(\<Sum>xk\<in>UNIV. count_list (resolve_store B m xk) a)
       = (\<Sum>(x, k)\<in>iterate_range B. count_list (resolve_store_nat m (x, k)) a)"
  by (simp add: resolve_store_def compS_apply iterate_range_def inj_to_nat sum.reindex)

lemma sum_decompose_first_step:
  fixes m :: "('y::enum, 'b) update"
  fixes B :: "'k::enum boundedness"
  assumes "boundedness B K"
  assumes "bounded K m"
  shows "(\<Sum>(x, k)\<in>iterate_range B. count_list (resolve_store_nat m (x, k)) a)
       = (\<Sum>(x, k)\<in>(\<Union>y\<in>UNIV. set (valuate (synthesize_shuffle_nat (resolve_shuffle m) y))).
            count_list (resolve_store_nat m (x, k)) a)"
proof (rule sum.mono_neutral_right, auto)
  fix x0 k0 y
  assume *: "(x0, k0) \<in> set (valuate (synthesize_shuffle_nat (resolve_shuffle m) y))"
  show "(x0, k0) \<in> iterate_range B"
  proof (cases k0)
    case None
    then show ?thesis by simp
  next
    case (Some k)
    have "bounded_shuffle K (resolve_shuffle m)" using assms(2) by (rule resolve_bounded)
    then show ?thesis using assms(1) * bounded_shuffle_less_than
      apply (simp add: Some synthesize_shuffle_nat_def) by fastforce
  qed
next
  fix x0 k0
  assume asm: "\<forall>y. (x0, k0) \<notin> set (valuate (synthesize_shuffle_nat (resolve_shuffle m) y))"
  show "count_list (resolve_store_nat m (x0, k0)) a = 0"
  proof (cases k0)
    case None
    then have "(x0, None) \<notin> set (valuate (synthesize_shuffle_nat (resolve_shuffle m) x0))" using asm by simp
    then show ?thesis by (simp add: synthesize_shuffle_nat_def None)
  next
    case (Some k)
    obtain y0 where y0: "lookup_rec m x0 k Enum.enum 
         = lookup_row (resolve_shuffle m) x0 k (seek y0 Enum.enum) (scan_pair (m y0))"
      using enum_distinct enum_ne_Nil lookup_rec_distinct by fast 
    moreover have "(x0, k0) \<notin> set (valuate (synthesize_shuffle_nat (resolve_shuffle m) y0))"
      using asm by simp
    ultimately show "count_list (resolve_store_nat m (x0, k0)) a = 0"
      by (simp add: Some there_doesnt_exist_corresponding_string synthesize_shuffle_nat_def)
  qed
qed

lemma sum_UNION_eq_sum_sum_list:
  assumes "distinct ys"
  assumes "distinct (concat (map f ys))"
  shows "(\<Sum>x\<in>(\<Union>y\<in>set ys. set (f y)). g x) = (\<Sum>y\<in>set ys. \<Sum>x\<leftarrow>f y. g x)"
  using assms  by (induct ys, simp_all add: sum.union_disjoint sum.distinct_set_conv_list)

lemma count_list_sum_list_concat_map:
  "(\<Sum>x\<leftarrow>xs. count_list (g x) a) = count_list (concat (map g xs)) a"
  by (induct xs, simp_all)


lemma distinct_post_index_vars:
  "distinct (post_index_vars s ys xs)"
proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case proof (auto)
    assume "(x, Some (calc_index s ys xs x)) \<in> set (post_index_vars s ys xs)"
    then have "calc_index s ys xs x < calc_index s ys xs x"
      by (rule give_index_row_position_lt)
    then show False by simp
  qed
qed


lemma post_index_vars_seek_contr:
  assumes "y0 \<in> set ys"
  assumes "(x0, Some k0) \<in> set (post_index_vars s (seek y0 ys) (s y0))"
  assumes "(x0, Some k0) \<in> set (post_index_vars s ys (s y1))"
  shows "False"
proof -
  have "k0 < calc_index s (seek y0 ys) (s y0) x0"
    using assms(2) by (rule give_index_row_position_lt)
  also have "... \<le> calc_index_rows s ys x0"
    using assms(1) by (rule calc_index_rows_seek)
  finally have "k0 < calc_index_rows s ys x0" .
  also have "k0 \<ge> calc_index_rows s ys x0"
    using assms(3) by (rule give_index_row_position_ge)
  finally show False by simp
qed

lemma seek_twice:
  assumes "y0 \<noteq> y1"
  shows "seek y0 (seek y1 ys) = seek y0 ys
       \<or> seek y1 (seek y0 ys) = seek y1 ys"
  using assms by (induct ys, simp_all)

lemma seek_length_le:
  "length (seek y ys) \<le> length ys"
  by (induct ys, auto)

lemma seek_in_neq:
  assumes "y2 \<in> set ys"
  shows "seek y1 (seek y2 ys) \<noteq> ys"
proof -
  have "length (seek y1 (seek y2 ys)) \<le> length (seek y2 ys)"
    by (simp add: seek_length_le)
  also have "... < length ys" using assms
    by (induct ys, auto)
  finally show ?thesis by auto
qed


lemma post_index_vars_not_in_two_rows_aux:
  assumes neq: "y1 \<noteq> y2"
  assumes y1: "y1 \<in> set ys"
  assumes y2: "y2 \<in> set ys"
  assumes in1: "(x0, Some k0) \<in> set (post_index_vars s (seek y1 ys) (s y1))"
  assumes in2: "(x0, Some k0) \<in> set (post_index_vars s (seek y2 ys) (s y2))"
  assumes *: "seek y1 (seek y2 ys) = seek y1 ys"
  shows False
proof -
  have 1: "(x0, Some k0) \<in> set (post_index_vars s (seek y1 (seek y2 ys)) (s y1))"
    using in1 * by simp
  have in_y1: "y1 \<in> set (seek y2 ys)" using neq y1 y2 * proof (induct ys)
    case Nil
    then show ?case by simp
  next
    case (Cons a ys)
    then show ?case by (cases "a = y1"; cases "a = y2", simp_all add: seek_in_neq)
  qed
  show False using post_index_vars_seek_contr in_y1 1 in2 by fast
qed


lemma post_index_vars_not_in_two_rows:
  assumes neq: "y1 \<noteq> y2"
  assumes y1: "y1 \<in> set ys"
  assumes y2: "y2 \<in> set ys"
  assumes in1: "(x0, Some k0) \<in> set (post_index_vars s (seek y1 ys) (s y1))"
  assumes in2: "(x0, Some k0) \<in> set (post_index_vars s (seek y2 ys) (s y2))"
  shows False
  using seek_twice[OF neq] proof
  assume *: "seek y1 (seek y2 ys) = seek y1 ys"
  show False using post_index_vars_not_in_two_rows_aux[OF assms *] by simp
next
  assume *: "seek y2 (seek y1 ys) = seek y2 ys"
  show False using post_index_vars_not_in_two_rows_aux[OF neq[symmetric] y2 y1 in2 in1 *] by simp
qed


lemma synthesize_shuffle_nat_not_contain_two_rows:
  assumes neq: "y0 \<noteq> y1"
  assumes "(x0, k0) \<in> set (valuate (synthesize_shuffle_nat s y0))"
  assumes "(x0, k0) \<in> set (valuate (synthesize_shuffle_nat s y1))"
  shows False
proof (cases k0)
  case None
  then show ?thesis using assms
    by (simp add: synthesize_shuffle_nat_def post_index_vars_does_not_contain_None)
next
  case (Some k)
  have y0: "y0 \<in> set Enum.enum" by (simp add: enum_UNIV)
  have y1: "y1 \<in> set Enum.enum" by (simp add: enum_UNIV)
  have in1: "(x0, Some k) \<in> set (post_index_vars s (seek y0 Enum.enum) (s y0))" using assms by (simp add: synthesize_shuffle_nat_def Some)
  have in2: "(x0, Some k) \<in> set (post_index_vars s (seek y1 Enum.enum) (s y1))" using assms by (simp add: synthesize_shuffle_nat_def Some)
  show ?thesis using post_index_vars_not_in_two_rows[OF neq y0 y1 in1 in2] by simp
qed


lemma distinct_synthesize_shuffle:
  fixes m :: "('y::enum, 'b) update"
  fixes B :: "'k::enum boundedness"
  assumes "distinct ys"
  shows "distinct (concat (map (\<lambda>y. valuate (synthesize_shuffle_nat (resolve_shuffle m) y)) ys))"
  using assms proof (induct ys)
  case Nil
  then show ?case by simp
next
  case (Cons y0 ys)
  have y_notin_ys: "y0 \<notin> set ys" using Cons.prems by simp
  have distinct_ys: "distinct ys" using Cons.prems by simp
  then have distinct_rest: "distinct (concat (map (\<lambda>y. valuate (synthesize_shuffle_nat (resolve_shuffle m) y)) ys))"
    using Cons.hyps by simp
  have distinct_row: "distinct (valuate (synthesize_shuffle_nat (resolve_shuffle m) y0))"
    using distinct_post_index_vars by (simp add: synthesize_shuffle_nat_def post_index_vars_does_not_contain_None distinct_post_index_vars)
  show ?case proof (simp add: valuate_hat_alpha Cons post_index_vars_does_not_contain_None y_notin_ys distinct_row distinct_rest, auto)
    fix x k y
    assume y0: "(x, k) \<in> set (valuate (synthesize_shuffle_nat (resolve_shuffle m) y0))"
    assume y: "(x, k) \<in> set (valuate (synthesize_shuffle_nat (resolve_shuffle m) y))"
    assume ys: "y \<in> set ys"
    have neq: "y \<noteq> y0" using y_notin_ys ys by auto
    show False using synthesize_shuffle_nat_not_contain_two_rows[OF neq y y0] by simp
  qed
qed

lemma resolve_inverse_nat_valuate: 
  "concat (map (resolve_store_nat m) (valuate (synthesize_shuffle_nat (resolve_shuffle m) x))) = valuate (m x)"
proof -
  have "(resolve_store_nat m \<odot> (valuate o synthesize_shuffle_nat (resolve_shuffle m))) x = valuate (m x)"
    by (simp add: valuate_map_alpha[symmetric] resolve_inverse_nat)
  then show ?thesis by (simp add: compS_apply)
qed

lemma count_list_valuate: "count_list (valuate u) a = count_list u (Inr a)"
  by (induct u rule: xa_induct, simp_all)

lemma sum_decompose:
  fixes m :: "('y::enum, 'b) update"
  fixes B :: "'k::enum boundedness"
  assumes "boundedness B K"
  assumes "bounded K m"
  shows "(\<Sum>yk\<in>UNIV. count_list (resolve_store B m yk) a)
       = (\<Sum>y\<in>UNIV. count_list (m y) (Inr a))" (is "?from = ?to")
proof -
  let ?vars = "\<lambda>y. valuate (synthesize_shuffle_nat (resolve_shuffle m) y)"
  let ?resolve = "\<lambda>xk. resolve_store_nat m xk"
  let ?count = "\<lambda>xk. count_list (?resolve xk) a"
  have "?from = (\<Sum>xk\<in>iterate_range B. ?count xk)"
    using sum_decompose_to_nat by simp
  also have "... = (\<Sum>xk\<in>(\<Union>y\<in>UNIV. set (?vars y)). ?count xk)"
    using sum_decompose_first_step[OF assms] by simp
  also have "... = (\<Sum>y\<in>UNIV. \<Sum>xk\<leftarrow>?vars y. ?count xk)"
    apply (simp only: UNIV_enum)
    apply (rule sum_UNION_eq_sum_sum_list[OF enum_distinct])
    apply (rule distinct_synthesize_shuffle[OF enum_distinct])
    done
  also have "... = (\<Sum>y\<in>UNIV. count_list (concat (map ?resolve (?vars y))) a)"
    by (simp add: count_list_sum_list_concat_map)
  also have "... = ?to"
    using resolve_inverse_nat_valuate by (simp add: compS_apply resolve_inverse_nat_valuate count_list_valuate)
  finally show ?thesis .
qed


theorem convert_MSST_bounded:
  fixes msst :: "('q::finite, 'x::finite, 'y::enum, 'a, 'b) MSST"
  fixes B1 :: "'k::enum boundedness"
  fixes B2 :: "'l::enum boundedness"
  assumes bc_msst: "bounded_copy_SST k msst"
  assumes boundedness_k: "boundedness B1 k"
  assumes boundedness_l: "boundedness B2 l"
  assumes typed: "is_type msst \<gamma>"
  assumes bc_type: "bounded_copy_type l msst \<gamma>"
  shows "bounded_copy_SST (k * l) (convert_MSST B2 msst)"
  unfolding bounded_copy_SST_def bounded_def
proof (intro allI, rule impI)
  fix w qb
  assume "reachable (convert_MSST B2 msst) qb"
  then have r_pair: "reachable (convert_MSST B2 msst) (fst qb, snd qb)" by simp
  then have r_fst: "reachable msst (fst qb)" by (rule reachable_convert)
  have l0: "0 < l" using assms length_enum_gt_0 unfolding boundedness_def by simp
  have k0: "0 < k" using assms length_enum_gt_0 unfolding boundedness_def by simp

  show "\<forall>y. count_var (SST.eta_hat (convert_MSST B2 msst) (qb, w)) y \<le> k * l"
  proof (cases "length w")
    case 0
    then show ?thesis
      apply simp unfolding count_var_def idU_def 
      apply (simp only: sum_count_list_inj[OF inj_Inl])
      apply (simp add: k0 l0 Suc_leI)
      done
  next
    case (Suc nat)
    then have w_gt_0: "0 < length w" by simp
    note mado = convert_\<eta>_hat_gt_0[OF assms(3-5) r_pair w_gt_0, simplified]
    then show ?thesis proof (auto simp add: mado count_var_def H'_def prod.case_eq_if)
      fix x0 y0 z0
      have "(\<Sum>xyz\<in>UNIV. count_list (resolve_store B2 (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb)))
                                                                (SST.eta_hat msst (fst qb, w) (fst xyz))) (snd xyz))
           (Inl (x0, y0, z0)))
          = (\<Sum>(x, yk)\<in>UNIV. count_list (resolve_store B2 (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x)) yk)
           (Inl (x0, y0, z0)))" (is "?lhs = _")
        by (simp add: prod.case_eq_if)
      also have "... = (\<Sum>x\<in>UNIV. \<Sum>yk\<in>UNIV. count_list (resolve_store B2 (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x)) yk)
           (Inl (x0, y0, z0)))"
        apply (simp only: UNIV_Times_UNIV[symmetric])
        apply (rule sum.Sigma[symmetric], simp_all)
        done
      also have "... = (\<Sum>x\<in>UNIV. \<Sum>y\<in>UNIV. count_list (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x) y)
           (Inr (Inl (x0, y0, z0))))"
        by (simp add: sum_decompose[OF boundedness_l hat_homU_iota_bounded_copy[OF boundedness_l typed bc_type r_pair]])
      also have "... = (\<Sum>x\<in>UNIV. count_alpha (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x)) (Inl (x0, y0, z0)))"
        unfolding count_alpha_def by simp
      also have "... \<le> k * l" proof -
        have body: "\<And>x. count_alpha (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x)) (Inl (x0, y0, z0))
                    \<le> count_list (SST.eta_hat msst (fst qb, w) x) (Inl x0) * l" proof -
          fix x
          have tail: "SST.eta_hat msst (fst qb, w) x \<in> tails (SST.eta_hat msst (fst qb, w) x)"
            unfolding tails_def by auto
          show "count_alpha (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x)) (Inl (x0, y0, z0))
                    \<le> count_list (SST.eta_hat msst (fst qb, w) x) (Inl x0) * l"
            by (simp add: count_alpha_hat_homU_eta_hat[OF bc_msst boundedness_l typed bc_type r_pair tail])
        qed
        have "(\<Sum>x\<in>UNIV. count_alpha (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x)) (Inl (x0, y0, z0)))
            \<le> (\<Sum>x\<in>UNIV. count_list (SST.eta_hat msst (fst qb, w) x) (Inl x0) * l)"
          by (simp add: body sum_mono)
        also have "... = (\<Sum>x\<in>UNIV. count_list (SST.eta_hat msst (fst qb, w) x) (Inl x0)) * l"
          by (metis (mono_tags, lifting) sum.cong sum_distrib_right)
        also have "... = count_var (SST.eta_hat msst (fst qb, w)) x0 * l"
          unfolding count_var_def by simp
        also have "... \<le> k * l" proof -
          have "bounded k (SST.eta_hat msst (fst qb, w))"
            using bc_msst r_fst unfolding bounded_copy_SST_def by auto
          then have "count_var (SST.eta_hat msst (fst qb, w)) x0 \<le> k"
            by (simp add: bounded_def)
          then show ?thesis by simp
        qed
        finally show ?thesis .
      qed
      finally show "?lhs \<le> k * l" .
    qed
  qed
qed

lemma "f (g x :: 'a list) = h (g x)"
proof -
  fix u
  show "f u = h u" proof (induct "(g x)")

  


end
