theory Bounded_Copy_Convert
  imports Main HOL.Finite_Set
          "../Util/Enum_Nat" "../Core/Update" "../Single_Use/Single_Use" "../Decomposition/Decompose_Update"
          "../Composition/Convert_Monoid_SST" "../Type/Monoid_SST_Type"
begin



definition valid_vars :: "'k::enum boundedness \<Rightarrow> ('y \<times> nat option) set"  where
  "valid_vars B = (UNIV :: 'y set) \<times> (insert None (Some ` {k. k < length (Enum.enum :: 'k list)}))"


lemma valid_vars_eq_range:
  "(valid_vars B :: ('y \<times> nat option) set) = range (to_nat B)"
proof
  show "(valid_vars B :: ('y \<times> nat option) set) \<subseteq> range (to_nat B)" proof (rule subsetI, rule range_eqI)
    fix yk
    assume *: "yk \<in> (valid_vars B :: ('y \<times> nat option) set)"
    then show "yk = to_nat B (to_enum B yk)"
      by (cases yk rule: index_cases, simp_all add: valid_vars_def inj_image_mem_iff nat_enum_iso)
  qed
next
  show "range (to_nat B) \<subseteq> (valid_vars B :: ('y \<times> nat option) set)"
  proof
    fix yk :: "'y \<times> nat option"
    assume "yk \<in> range (to_nat B)"
    then obtain xk where "to_nat B xk = yk" by blast
    then show "yk \<in> valid_vars B" unfolding valid_vars_def by (cases xk rule: index_cases, auto simp add: enum_nat_less)
  qed
qed

lemma valid_vars_finite[simp]:
  "finite (valid_vars B :: ('y::finite \<times> nat option) set)"
  unfolding valid_vars_def by simp

lemma valid_vars_None[simp]:
  "(y::'y::enum, None) \<in> valid_vars (B :: 'k::enum boundedness)"
  unfolding valid_vars_def by simp

lemma valid_vars_Some[simp]:
  fixes B :: "'k::enum boundedness"
  assumes "boundedness B K"
  assumes "k < K"
  shows "(y::'y::enum, Some k) \<in> valid_vars B"
  using assms unfolding boundedness_def valid_vars_def by simp

lemma distinct_count_list_le_1:
  assumes "distinct xs"
  shows "count_list xs a \<le> Suc 0"
using assms proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases "x = a", simp_all)
qed


definition update_index_vars where
  "update_index_vars m = concat (map (\<lambda>y. valuate (synthesize_shuffle_nat (\<pi>\<^sub>1 m) y)) Enum.enum)"

lemma update_index_vars_set:
  "set (update_index_vars m) = (\<Union>y\<in>UNIV. set (valuate (synthesize_shuffle_nat (resolve_shuffle m) y)))"
  unfolding update_index_vars_def
  by (simp add: enum_UNIV)

lemma sum_count_list_concat_map:
  assumes "distinct xs"
  shows "(\<Sum>x\<in>set xs. count_list (f x) a) = count_list (concat (map f xs)) a"
  using assms by (induct xs, simp_all)


(* disjointness BEGIN *)

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


lemma distinct_synthesize_shuffle_nat:
  fixes m :: "('y::enum, 'b) update"
  fixes B :: "'k::enum boundedness"
  assumes "distinct ys" 
  shows "distinct (concat (map (\<lambda>y. valuate (synthesize_shuffle_nat s y)) ys))"
  using assms proof (induct ys)
  case Nil
  then show ?case by simp
next
  case (Cons y0 ys)
  have y_notin_ys: "y0 \<notin> set ys" using Cons.prems by simp
  have distinct_ys: "distinct ys" using Cons.prems by simp
  then have distinct_rest: "distinct (concat (map (\<lambda>y. valuate (synthesize_shuffle_nat s y)) ys))"
    using Cons.hyps by simp
  have distinct_row: "distinct (valuate (synthesize_shuffle_nat s y0))"
    using distinct_post_index_vars by (simp add: synthesize_shuffle_nat_def post_index_vars_does_not_contain_None distinct_post_index_vars)
  show ?case proof (simp add: valuate_hat_alpha Cons post_index_vars_does_not_contain_None y_notin_ys distinct_row distinct_rest, auto)
    fix x k y
    assume y0: "(x, k) \<in> set (valuate (synthesize_shuffle_nat s y0))"
    assume y: "(x, k) \<in> set (valuate (synthesize_shuffle_nat s y))"
    assume ys: "y \<in> set ys"
    have neq: "y \<noteq> y0" using y_notin_ys ys by auto
    show False using synthesize_shuffle_nat_not_contain_two_rows[OF neq y y0] by simp
  qed
qed

lemma distinct_index_vars:
  "distinct (update_index_vars m)"
  unfolding update_index_vars_def
  by (rule distinct_synthesize_shuffle_nat[OF enum_distinct])


(* END disjointness *)








lemma count_alpha_synthesize_shuffle_nat:
  fixes s :: "('y::enum) shuffle"
  shows "count_alpha (synthesize_shuffle_nat s) yk \<le> 1"
proof (cases yk rule: index_cases)
  case (VarNone y)
  then show ?thesis
    apply (simp add: count_list_valuate[symmetric] count_list_my_simp VarNone sum.distrib count_alpha_def synthesize_shuffle_nat_def
                      post_index_vars_does_not_contain_None del: count_list.simps)
    apply (simp add: kronecker_def)
    done
next
  case (VarSome y k)
  show ?thesis
    apply (simp add: count_alpha_def UNIV_enum sum_count_list_concat_map[OF enum_distinct])
    apply (rule distinct_count_list_le_1)
    apply (rule distinct_synthesize_shuffle_nat)
    apply (rule enum_distinct)
    done
qed


lemma [simp]:
  "concat (map (embed x) xs) = map (embed_single x) xs"
  by (induct xs, simp_all)

lemma inj_on_map_option:
  assumes "inj_on f A"
  shows "inj_on (map_option f) (insert None (Some ` A))"
  using assms by (auto simp add: inj_on_def)
  
lemma count_list_inj_on:
  assumes "inj_on f A"
  assumes "a \<in> A"
  assumes "set xs \<subseteq> A"
  shows "count_list (map f xs) (f a) = count_list xs a"
  using assms(3) proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case using assms(1-2) by (simp add: inj_on_def)
qed



lemma embed_single_inj: "inj (embed_single x)" unfolding inj_on_def by simp

lemma to_enum_inj_on: "inj_on (to_enum B) (valid_vars B :: ('y::enum \<times> nat option) set)"
  apply (simp only: valid_vars_def inj_on_apsnd to_enum.simps)
  apply (rule inj_on_map_option)
  apply (rule inj_nat_to_enum)
  done

lemma to_nat_inj: "inj (to_nat B :: ('y \<times> 'k::enum option \<Rightarrow> 'y \<times> nat option))"
  unfolding inj_on_def
proof (intro ballI, rule impI)
  fix x y :: "'y \<times> 'k option"
  assume "to_nat B x = to_nat B y"
  then show "x = y"
    apply (cases x rule: index_cases; cases y rule: index_cases; simp_all)
    using inj_enum_to_nat unfolding inj_on_def by auto
qed
    

lemma count_list_embed_single:
  "count_list (map (embed_single x) u) (Inl (x, y, z)) = count_list u (y, z)"
proof -
  have *: "Inl (x, y, z) = embed_single x (y, z)" by simp
  show ?thesis
    apply (simp add: * del: embed_single.simps)
    apply (rule count_list_inj_on[where A="UNIV"], simp_all add: embed_single_inj)
    done
qed

lemma count_list_to_enum:
  assumes "boundedness B K"
  assumes "list_all (index_less_than K) u"
  shows "count_list (map (to_enum B) u) (y, z) = count_list u (to_nat B (y, z))"
proof -
  have "count_list (map (to_enum B) u) (y, z)
      = count_list (map (to_nat B) (map (to_enum B) u)) (to_nat B (y, z))"
    by (rule count_list_inj_on[where A=UNIV, symmetric], simp_all add: to_nat_inj)
  moreover have "map (to_nat B) (map (to_enum B) u) = u"
    using assms(2) proof (induct u)
    case Nil
    then show ?case by simp
  next
    case (Cons a u)
    then show ?case proof (cases a rule: index_cases)
      case (VarNone y)
      then show ?thesis using Cons by simp
    next
      case (VarSome y k)
      then show ?thesis using Cons assms(1) unfolding boundedness_def by (simp add: nat_enum_iso)
    qed
  qed
  ultimately show ?thesis by simp
qed

lemma synthesize_shuffle_nat_index_less_than:
  assumes "bounded_shuffle K s"
  shows "list_all (index_less_than K) (valuate (synthesize_shuffle_nat s xk))"
  by (simp add: synthesize_shuffle_nat_def, rule bounded_shuffle_index_less_than, rule assms)


lemma count_alpha_iota_le_1:
  fixes \<alpha> :: "'x \<Rightarrow> 'y::enum shuffle"
  assumes "boundedness (B :: 'k::enum boundedness) k"
  assumes "bounded_shuffle k (\<alpha> x)"
  shows "count_alpha (\<iota> B \<alpha> x :: ('y, 'x \<times> ('y, 'k::enum) index + 'b) update) (Inl (x, y0, z0) :: 'x \<times> ('y, 'k::enum) index + 'b) \<le> 1"
  apply (simp add: \<iota>_def synthesize_def count_alpha_def valuate_hat_alpha map_alpha_apply count_list_my_simp del: map_map count_list.simps to_enum.simps)
  apply (simp add: count_list_embed_single del: map_map to_enum.simps)
  apply (simp add: count_list_to_enum[OF assms(1) synthesize_shuffle_nat_index_less_than[OF assms(2)]] del: to_enum.simps)
  apply (simp add: UNIV_enum sum_count_list_concat_map[OF enum_distinct])
  apply (rule distinct_count_list_le_1)
  apply (rule distinct_synthesize_shuffle_nat[OF enum_distinct])
  done

lemma embed_single_notin:
  assumes "x \<noteq> x0"
  shows "Inl (x0, y0, z0) \<notin> set (map (embed_single x) u)"
  using assms by (induct u, simp_all)

lemma count_alpha_iota_x_neq_x0_eq_0:
  fixes \<alpha> :: "'x \<Rightarrow> 'y::enum shuffle"
  assumes "x \<noteq> x0"
  assumes "boundedness (B :: 'k::enum boundedness) k"
  assumes "bounded_shuffle k (\<alpha> x)"
  shows "count_alpha (\<iota> B \<alpha> x :: ('y, 'x \<times> ('y, 'k::enum) index + 'b) update) (Inl (x0, y0, z0) :: 'x \<times> ('y, 'k::enum) index + 'b) = 0"
  apply (simp add: \<iota>_def synthesize_def count_alpha_def valuate_hat_alpha map_alpha_apply del: map_map to_enum.simps)
  apply (rule allI)
  apply (rule count_notin)
  apply (rule embed_single_notin)
  apply (rule assms(1))
  done

lemma count_list_inr_list_Inl: "count_list (valuate (hat_alpha inr_list w)) (Inl xyz) = 0"
  by (induct w rule: xa_induct, simp_all)

lemma count_alpha_inr_list: "count_alpha (inr_list \<star> a) (Inl xyz) = 0"
  unfolding count_alpha_def map_alpha_def by (simp add: count_list_inr_list_Inl)

lemma count_alpha_hat_homU_eta_hat:
  fixes msst :: "('q::finite, 'x::finite, 'y::enum, 'a, 'b) MSST"
  fixes B1 :: "'k::enum boundedness"
  fixes B2 :: "'l::enum boundedness"
  assumes bc_msst: "bounded_copy_SST k msst"
  assumes boundedness_l: "boundedness B2 l"
  assumes bc_type: "bctype l msst \<gamma>"
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
      obtain ys where "ys @ Inl x' # xs = SST.eta_hat msst (q1, w) x"
        using Var.prems unfolding tails_def by auto
      then have body: "SST.eta_hat msst (q1, w) x = (ys @ [Inl x']) @ xs" by simp
      show ?thesis unfolding tails_def by (simp, rule exI[where x="ys @ [Inl x']"], rule body)
    qed
    note IH = Var.hyps(1)[OF xs]
    have rep: "Rep_alpha B2 \<beta> x' \<in> \<gamma> (q1, x')"
      by (rule condition_of_convert_MSST_reachable_state[OF boundedness_l bc_type reach])
    have "reachable msst q1" using reach by (rule reachable_convert)
    then have bs: "bounded_shuffle l (Rep_alpha B2 \<beta> x')"
      using bc_type rep by (simp add: bctype_bounded)
    note bc = hat_homU_iota_bounded_copy_tail[OF boundedness_l bc_type reach xs]
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



lemma sum_decompose_to_nat:
  fixes m :: "('y::enum, 'b) update"
  fixes B :: "'k::enum boundedness"
  shows "(\<Sum>xk\<in>UNIV. count_list (resolve_store B m xk) a)
       = (\<Sum>xk\<in>valid_vars B. count_list (resolve_store_nat m xk) a)"
proof -
  have "(\<Sum>xk\<in>UNIV. count_list (resolve_store B m xk) a)
      = (\<Sum>xk\<in>range (to_nat B). count_list (resolve_store_nat m xk) a)"
    unfolding resolve_store_def 
    by (simp add: compS_apply sum.reindex to_nat_inj)
  also have "... = (\<Sum>xk\<in>valid_vars B. count_list (resolve_store_nat m xk) a)"
    by (simp add: valid_vars_eq_range)
  finally show ?thesis .
qed

lemma sum_decompose_first_step:
  fixes m :: "('y::enum, 'b) update"
  fixes B :: "'k::enum boundedness"
  assumes "boundedness B K"
  assumes "bounded K m"
  shows "(\<Sum>(x, k)\<in>valid_vars B. count_list (resolve_store_nat m (x, k)) a)
       = (\<Sum>(x, k)\<in>set (update_index_vars m).
            count_list (resolve_store_nat m (x, k)) a)"
proof (simp add: update_index_vars_set, rule sum.mono_neutral_right, auto)
  fix x0 k0 y
  assume *: "(x0, k0) \<in> set (valuate (synthesize_shuffle_nat (resolve_shuffle m) y))"
  show "(x0, k0) \<in> valid_vars B"
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




lemma resolve_inverse_nat_valuate: 
  "concat (map (resolve_store_nat m) (valuate (synthesize_shuffle_nat (resolve_shuffle m) x))) = valuate (m x)"
proof -
  have "(resolve_store_nat m \<odot> (valuate o synthesize_shuffle_nat (resolve_shuffle m))) x = valuate (m x)"
    by (simp add: valuate_map_alpha[symmetric] resolve_inverse_nat)
  then show ?thesis by (simp add: compS_apply)
qed



lemma sum_decompose:
  fixes m :: "('y::enum, 'b) update"
  fixes B :: "'k::enum boundedness"
  assumes "boundedness B K"
  assumes "bounded K m"
  shows "(\<Sum>yk\<in>UNIV. count_list (resolve_store B m yk) a)
       = (\<Sum>y\<in>UNIV. count_list (valuate (m y)) a)" (is "?from = ?to")
proof -
  let ?vars = "\<lambda>y. valuate (synthesize_shuffle_nat (resolve_shuffle m) y)"
  let ?resolve = "\<lambda>xk. resolve_store_nat m xk"
  let ?count = "\<lambda>xk. count_list (?resolve xk) a"
  have "?from = (\<Sum>xk::'y \<times> nat option\<in>valid_vars B. ?count xk)"
    by (simp add: sum_decompose_to_nat)
  also have "... = (\<Sum>xk\<in>(\<Union>y\<in>UNIV. set (?vars y)). ?count xk)"
    using sum_decompose_first_step[OF assms] by (simp add: update_index_vars_set)
  also have "... = (\<Sum>y\<in>UNIV. \<Sum>xk\<leftarrow>?vars y. ?count xk)"
    apply (simp only: UNIV_enum)
    apply (rule sum_UNION_eq_sum_sum_list[OF enum_distinct])
    apply (rule distinct_synthesize_shuffle_nat[OF enum_distinct])
    done
  also have "... = (\<Sum>y\<in>UNIV. count_list (concat (map ?resolve (?vars y))) a)"
    by (simp add: count_list_sum_list_concat_map)
  also have "... = ?to"
    using resolve_inverse_nat_valuate by (simp add: compS_apply resolve_inverse_nat_valuate)
  finally show ?thesis .
qed


theorem convert_MSST_bounded:
  fixes msst :: "('q::finite, 'x::finite, 'y::enum, 'a, 'b) MSST"
  fixes B1 :: "'k::enum boundedness"
  fixes B2 :: "'l::enum boundedness"
  assumes bc_msst: "bounded_copy_SST k msst"
  assumes boundedness_k: "boundedness B1 k"
  assumes boundedness_l: "boundedness B2 l"
  assumes bc_type: "bctype l msst \<gamma>"
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
      apply (simp)
      apply (simp only: count_list.simps)
      apply (simp add: k0 l0 Suc_leI)
      done
  next
    case (Suc nat)
    then have w_gt_0: "0 < length w" by simp
    note mado = convert_\<eta>_hat_gt_0[OF boundedness_l bc_type r_pair w_gt_0, simplified]
    then show ?thesis proof (auto simp add: mado count_var_def H'_def prod.case_eq_if delta_convert_MSST_simp eta_convert_MSST_simp)
      fix x0 y0 z0
      have "(\<Sum>xyz\<in>UNIV. count_list (extract_variables (resolve_store B2 (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb)))
                                                          (SST.eta_hat msst (fst qb, w) (fst xyz))) (snd xyz)))
           (x0, y0, z0))
          = (\<Sum>(x, yk)\<in>UNIV. count_list (extract_variables (resolve_store B2 (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x)) yk))
           (x0, y0, z0))" (is "?lhs = _")
        by (simp add: prod.case_eq_if)
      also have "... = (\<Sum>x\<in>UNIV. \<Sum>yk\<in>UNIV. count_list (extract_variables (resolve_store B2 (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x)) yk))
           (x0, y0, z0))"
        apply (simp only: UNIV_Times_UNIV[symmetric])
        apply (rule sum.Sigma[symmetric], simp_all)
        done
      also have "... = (\<Sum>x\<in>UNIV. \<Sum>y\<in>UNIV. count_list (valuate (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x) y))
           (Inl (x0, y0, z0)))"
        by (simp add: count_list_extract_variables sum_decompose[OF boundedness_l hat_homU_iota_bounded_copy[OF boundedness_l bc_type r_pair]])
      also have "... = (\<Sum>x\<in>UNIV. count_alpha (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x)) (Inl (x0, y0, z0)))"
        unfolding count_alpha_def by simp
      also have "... \<le> k * l" proof -
        have body: "\<And>x. count_alpha (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x)) (Inl (x0, y0, z0))
                    \<le> count_list (extract_variables (SST.eta_hat msst (fst qb, w) x)) x0 * l" proof -
          fix x
          have tail: "SST.eta_hat msst (fst qb, w) x \<in> tails (SST.eta_hat msst (fst qb, w) x)"
            unfolding tails_def by auto
          show "count_alpha (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x)) (Inl (x0, y0, z0))
                    \<le> count_list (extract_variables (SST.eta_hat msst (fst qb, w) x)) x0 * l"
            by (simp add: count_list_extract_variables count_alpha_hat_homU_eta_hat[OF bc_msst boundedness_l bc_type r_pair tail])
        qed
        have "(\<Sum>x\<in>UNIV. count_alpha (hat_homU (\<iota> B2 (Rep_alpha B2 (snd qb))) (SST.eta_hat msst (fst qb, w) x)) (Inl (x0, y0, z0)))
            \<le> (\<Sum>x\<in>UNIV. count_list (extract_variables (SST.eta_hat msst (fst qb, w) x)) x0 * l)"
          by (simp add: body sum_mono)
        also have "... = (\<Sum>x\<in>UNIV. count_list (extract_variables (SST.eta_hat msst (fst qb, w) x)) x0) * l"
          by (simp add: sum_distrib_right)
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



end
