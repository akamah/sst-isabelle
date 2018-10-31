theory Bounded_Copy_Convert
  imports Main HOL.Finite_Set
          "../Util/Enum_Nat" "../Core/Update" "../Single_Use/Single_Use" "../Decomposition/Decompose_Update"
          "../Composition/Convert_Monoid_SST_Def" "../Type/Monoid_SST_Type"
begin

lemma count_list_flat:
  fixes a :: "'a"
  fixes sc :: "('y, 'a) scanned"
  assumes "length_scanned sc \<le> length (Enum.enum :: 'e::enum list)"
  shows "(\<Sum>k\<in>(UNIV::'e set). count_list (nth_string sc (enum_to_nat k)) a)
       = count_list (flat sc) (Inr a)"
using assms proof (induct sc rule: scanned_rev_induct)
  case (Nil w)
  then show ?case proof (simp)
    assume a0: "Suc 0 \<le> length (enum_class.enum :: 'e list)"
    have enum_nat_0: "enum_to_nat (nat_to_enum 0 :: 'e) = 0"
      by (rule nat_enum_iso, simp only: Suc_le_lessD a0)
    let ?g = "\<lambda>k::'e. count_list (nth_string ((w, []) :: ('y, 'a) scanned) (enum_to_nat k)) a"
    let ?k0 = "nat_to_enum 0 :: 'e"
    have "\<forall>k\<in>UNIV - {?k0}. ?g k = 0" proof
      fix k :: 'e
      assume a1: "k \<in> UNIV - {?k0}"
      have "0 < enum_to_nat k" proof (rule ccontr)
        assume "\<not> 0 < enum_to_nat k"
        then have "0 = enum_to_nat k" by simp
        then have k2: "?k0 = (nat_to_enum (enum_to_nat k))" by simp
        then have "?k0 = k" apply (simp add: k2) by (rule enum_nat_iso, simp add: UNIV_enum[symmetric])
        then have "k \<in> {?k0}" by simp
        then show False using a1 by simp
      qed
      then show "count_list (nth_string ((w, []) :: ('x, 'a) scanned) (enum_to_nat k)) a = 0"
        by (simp add: nth_string_pos_Nil)
    qed
    then have sum_0: "sum ?g ((UNIV::'e set) - {?k0}) = 0" by simp
    have "sum ?g (UNIV::'e set) = sum ?g ((UNIV::'e set) - {?k0}) + sum ?g {?k0}"
      by (rule sum.subset_diff, simp_all)
    also have "... = sum ?g {?k0}" using sum_0 by simp
    also have "... = count_list (map Inr w) (Inr a)" by (simp add: count_list_Inr nat_enum_iso enum_nat_0)
    finally show "sum ?g (UNIV::'e set) = count_list (map Inr w) (Inr a)" .
  qed
next
  case (PairSnoc x as sc)
  then show ?case proof simp
    let ?kn = "nat_to_enum (length_scanned sc) :: 'e"
    let ?Kn_1 = "{k::'e. length_scanned sc < enum_to_nat k}"
    assume "(\<Sum>k\<in>UNIV. count_list (nth_string sc (enum_to_nat k)) a) = count_list (flat sc) (Inr a)"
    assume "Suc (length_scanned sc) \<le> length (Enum.enum :: 'e list)"
    then have sc_len: "length_scanned sc < length (Enum.enum :: 'e list)" by simp
    then have kn: "enum_to_nat ?kn = length_scanned sc" by (simp add: nat_enum_iso)
    have kn_Kn_1: "?kn \<notin> ?Kn_1" by (simp add: nat_enum_iso sc_len)

    let ?f = "\<lambda>k::'e. count_list (nth_string (sc @@@ [(x, as)]) (enum_to_nat k)) a"
    let ?g = "\<lambda>k::'e. count_list (nth_string sc (enum_to_nat k)) a"

    have sum_fg: "sum ?f (UNIV - {?kn}) = sum ?g (UNIV - {?kn})" proof (rule sum.cong, auto)
      fix k :: "'e"
      have enum_nat_k: "nat_to_enum (enum_to_nat k) = k" by (rule enum_nat_iso, simp add: enum_UNIV)
      assume a0: "k \<noteq> ?kn"
      have a1: "enum_to_nat k \<noteq> length_scanned sc" proof (rule ccontr, simp)
        assume "enum_to_nat k = length_scanned sc"
        then have "nat_to_enum (enum_to_nat k) = ?kn" by simp
        then have "k = ?kn" by (simp add: enum_nat_k)
        then show False using a0 by simp
      qed
      then show "count_list (nth_string (sc @@@ [(x, as)]) (enum_to_nat k)) a 
               = count_list (nth_string sc (enum_to_nat k)) a" 
      proof (cases "enum_to_nat k < length_scanned sc")
        case True
        then show ?thesis by (simp add: nth_string_lt_length)
      next
        case False
        then have "length_scanned sc < enum_to_nat k" using a1 by simp
        then show ?thesis by (simp add: nth_string_ge_length)
      qed
    qed

    have sum_gn: "sum ?g {?kn} = 0" proof (simp add: kn nth_string_length)
      have "nth_string sc (length_scanned sc) = []" by (simp add: nth_string_ge_length)
      then show "count_list (nth_string sc (length_scanned sc)) a = 0" by simp
    qed

    have sum5: "sum ?g (UNIV - {?kn}) = sum ?g UNIV" proof -
      have            "sum ?g (UNIV - {?kn}) = sum ?g (UNIV - {?kn}) + sum ?g {?kn}" using sum_gn by simp
      also have "... = sum ?g UNIV" by (rule sum.subset_diff[symmetric], simp_all)
      finally show ?thesis .
    qed

    have            "sum ?f UNIV = sum ?f (UNIV - {?kn}) + sum ?f {?kn}" (is "?lhs = _")
      by (rule sum.subset_diff, simp_all)
    also have "... = sum ?g (UNIV - {?kn}) + sum ?f {?kn}"               
      using sum_fg by simp
    also have "... = sum ?g UNIV           + sum ?f {?kn}"              
      using sum5 by simp
    also have "... = count_list (flat sc) (Inr a :: 'y + 'a) + count_list (map Inr as) (Inr a :: 'y + 'a)" (is "_ = ?rhs")
      using PairSnoc by (simp add: kn count_list_Inr nth_string_append_last)
    finally show "?lhs = ?rhs" .
  qed
qed

lemma count_list_scan_flat:
  fixes a :: "'a"
  fixes m :: "('y::enum, 'a) update"
  fixes B :: "'k::enum boundedness"
  assumes "bounded k m"
  assumes "boundedness B k"
  shows "(\<Sum>y::'y\<in>UNIV. \<Sum>k\<in>(UNIV::('y, 'k) type_mult_suc set). count_list (nth_string (scan (m y)) (enum_to_nat k)) a)
       = (\<Sum>y::'y\<in>UNIV. count_list (m y) (Inr a))"
proof (rule sum.cong, simp_all)
  fix x :: "'y"
  have sc_len: "length_scanned (scan (m x)) \<le> length (Enum.enum :: ('y, 'k) type_mult_suc list)"
    using assms by (simp add: length_scanned_boundedness)
  show "(\<Sum>k::('y, 'k) type_mult_suc\<in>UNIV. count_list (nth_string (scan (m x)) (enum_to_nat k)) a)
      = count_list (m x) (Inr a)"
    by (simp add: count_list_flat sc_len scan_inverse)
qed

lemma sum_decompose:
  fixes m :: "('y::enum, 'b) update"
  fixes B :: "'k::enum boundedness"
  fixes a :: "'b"
  assumes "boundedness B k"
  assumes "bounded k m"
  shows "(\<Sum>yi\<in>(UNIV::('y, 'k) index set). count_list (resolve_store B m yi) a)
       = (\<Sum>y\<in>(UNIV::'y set). count_list (m y) (Inr a))"
proof -
  have "(\<Sum>yi\<in>(UNIV::('y, 'k) index set). count_list (resolve_store B m yi) a)
      = (\<Sum>y\<in>(UNIV::'y set). 
           \<Sum>k\<in>(UNIV::('y, 'k) type_mult_suc set). count_list (nth_string (scan (m y)) (enum_to_nat k)) a)"
    by (simp add: sum.Sigma resolve_store_def prod.case_eq_if)
  also have "... = (\<Sum>y\<in>(UNIV::'y set). count_list (m y) (Inr a))"
    using assms by (simp add: count_list_scan_flat)
  finally show ?thesis .
qed


lemma exist_only_list:
  assumes "count_list w x = 1"
  shows "\<exists>u v. (w = u @ x # v) \<and> (count_list u x = 0) \<and> (count_list v x = 0)"
using assms proof (induct w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case proof (cases "x = a")
    case True
    then show ?thesis using Cons.prems by (intro exI, auto)
  next
    case False
    then show ?thesis proof -
      have "count_list w x = 1" using Cons.prems False by simp
      then obtain u v where uv: "(w = u @ x # v) \<and> (count_list u x = 0) \<and> (count_list v x = 0)"
        using Cons.hyps by auto
      have "a # w = (a # u) @ x # v \<and> (count_list u x = 0) \<and> (count_list v x = 0)" using uv by simp
      then show ?thesis using False by fastforce
    qed
  qed
qed

thm padding_x

lemma "set (concat (map f u)) = (\<Union>x\<in>set u. set (f x))"
  by simp

definition pred_only_x_y:
  "pred_only_x_y x0 y0 yi = (\<forall>x y. (\<exists>k. yi = Inr (Inl (x, y, k))) \<longrightarrow> x = x0 \<and> y = y0)"

lemma pred_only_x_y_apply: "pred_only_x_y x0 y0 (Inr (Inl (x, y, z))) \<longleftrightarrow> x = x0 \<and> y = y0"
  unfolding pred_only_x_y by simp

lemma synthesize_store_padding_x_y:
  "list_all (pred_only_x_y x0 y0)
     (concat
       (map (synthesize_store B (Convert_Monoid_SST_Def.embed x0))
            (padding B y0 xas)))"
  unfolding synthesize_store_def pred_only_x_y 
  by (induct xas rule: scanned_rev_induct, simp_all)

lemma iota_x_y:
  "list_all (pred_only_x_y x0 y0) (\<iota> B \<alpha> x0 y0)"
  by (simp add: \<iota>_def synthesize_def synthesize_shuffle_def comp_def synthesize_store_padding_x_y)

lemma y_neq_y0_count_list_zero: "y \<noteq> y0 \<Longrightarrow> count_list (\<iota> B \<alpha> x y) (Inr (Inl (x0, y0, z0))) = 0"
proof -
  assume y_neq_y0: "y \<noteq> y0"
  have w: "\<forall>yi\<in>set (\<iota> B \<alpha> x y). pred_only_x_y x y yi"
    by (simp add: iota_x_y Ball_set_list_all)
  show ?thesis 
    by (metis count_notin pred_only_x_y_apply w y_neq_y0)
qed


lemma count_list_synthesize_ge_length:
  assumes "length_scanned (scan u) \<le> enum_to_nat (z0 :: ('y::enum, 'k::enum) type_mult_suc)"
  shows "count_list (concat (map (synthesize_store B (Convert_Monoid_SST_Def.embed x)) (padding B y (scan u))))
                    (Inr (Inl (x0, y0, z0)))
      = 0"
using assms proof (induct u rule: xw_induct)
  case (Word w)
  then show ?case by (auto simp add: synthesize_store_def nat_enum_zero)
next
  case (VarWord x w u)
  then show ?case proof (auto simp add: synthesize_store_def)
    let ?enum = "Enum.enum :: ('y, 'k) type_mult_suc list"
    have "enum_to_nat z0 < length ?enum" by (rule enum_nat_less)
    then have "Suc (length_scanned (scan u)) < length ?enum"
      using VarWord.prems by simp
    then have "length_scanned (scan u) < length (Enum.enum :: ('y, 'k) type_mult_suc list)"
      using Suc_lessD by blast
    then have len: "enum_to_nat (nat_to_enum (length_scanned (scan u)) :: ('y, 'k) type_mult_suc) = length_scanned (scan u) "
      by (simp add: nat_enum_iso)
    assume "Suc (length_scanned (scan u)) \<le> enum_to_nat (nat_to_enum (length_scanned (scan u)) :: ('y, 'k) type_mult_suc)"
    then show False using len by simp
  qed
qed

lemma count_list_append: "count_list (xs @ ys) a = count_list xs a + count_list ys a"
  by simp

lemma map_Cons: "map f [x] = f x # map Inr []" by simp

lemma count_list_synthesize_lt_length:
  assumes "length_scanned (scan u) \<le> length (Enum.enum::('y::enum, 'k) type_mult_suc list)"
  assumes "length_scanned (scan u) > enum_to_nat (z :: ('y::enum, 'k::enum) type_mult_suc)"
  shows "count_list (concat (map (synthesize_store B (Convert_Monoid_SST_Def.embed x)) (padding B y (scan u))))
                    (Inr (Inl (x, y, z)))
       = 1"
using assms proof (induct u rule: xw_induct)
  case (Word w)
  then show ?case by (simp add: synthesize_store_def nat_enum_zero enum_nat_zero_then_nat_enum_zero)
next
  case (VarWord x w u)
  then show ?case proof (cases "enum_to_nat z = length_scanned (scan u)")
    case True
    then show ?thesis proof -
      have *: "length_scanned (scan u) \<le> enum_to_nat z" using True by (simp add: )
      have z: "z \<in> set (Enum.enum :: ('y, 'k) type_mult_suc list)" by (simp add: enum_UNIV)
      thm count_list_synthesize_ge_length[OF *]
      show ?thesis
        apply (simp only: map_append scan_last_simp map_Cons padding_last_simp concat_append count_list_append)
        apply (simp add: count_list_synthesize_ge_length[OF *])
        apply (simp add: synthesize_store_def)
        apply (simp add: True[symmetric] enum_nat_iso[OF z])
        done
    qed
  next
    case False
    then show ?thesis using VarWord proof (simp add: synthesize_store_def)
      let ?enum = "Enum.enum :: ('y, 'k) type_mult_suc list"
      assume neq: "enum_to_nat z \<noteq> length_scanned (scan u)"
      have "length_scanned (scan u) \<le> length ?enum" using VarWord.prems by simp
      show "nat_to_enum (length_scanned (scan u)) \<noteq> z" proof (rule ccontr, simp)
        assume "nat_to_enum (length_scanned (scan u)) = z"
        then have "enum_to_nat (nat_to_enum (length_scanned (scan u)) :: ('y, 'k) type_mult_suc) = enum_to_nat z" by simp
        moreover have condition: "length_scanned (scan u) < length ?enum" using VarWord.prems by simp
        ultimately have "length_scanned (scan u) = enum_to_nat z" by (simp add: nat_enum_iso[OF condition])
        then show False using neq by simp
      qed
    qed
  qed
qed

lemma count_list_synthesize:
  assumes "length_scanned (scan u) \<le> length (Enum.enum::('y::enum, 'k::enum) type_mult_suc list)"
  shows "count_list (concat (map (synthesize_store B (Convert_Monoid_SST_Def.embed x)) (padding B y (scan u))))
                    (Inr (Inl (x, y, z :: ('y, 'k) type_mult_suc))) \<le> Suc 0"
proof (cases "length_scanned (scan u) \<le> enum_to_nat z")
  case True
  then show ?thesis by (simp add: count_list_synthesize_ge_length)
next
  case False
  then show ?thesis by (simp add: count_list_synthesize_lt_length assms)
qed

lemma count_alpha_iota_le_1:
  fixes \<alpha> :: "'x \<Rightarrow> 'y::enum shuffle"
  assumes "boundedness (B :: 'k::enum boundedness) k"
  assumes "bounded_shuffle k (\<alpha> x)"
  shows "count_alpha (\<iota> B \<alpha> x :: ('y, 'x \<times> ('y, 'k::enum) index + 'b) update) (Inl (x0, y0, z0) :: 'x \<times> ('y, 'k::enum) index + 'b) \<le> 1"
  unfolding count_alpha_def
proof (simp add:)
  let ?f = "\<lambda>y. count_list (\<iota> B \<alpha> x y) (Inr (Inl (x0, y0, z0)  :: 'x \<times> ('y::enum, 'k::enum) index + 'b))"
  let ?g = "\<lambda>y. if y = y0 then count_list (\<iota> B \<alpha> x y) (Inr (Inl (x0, y0, z0) :: 'x \<times> ('y::enum, 'k::enum) index + 'b)) else 0"
  have "sum ?f UNIV = sum ?g UNIV"
    by (rule sum.cong, simp_all add: iota_x_y y_neq_y0_count_list_zero)
  also have "... = ?f y0" 
    by simp
  also have "... \<le> Suc 0" proof (cases "x0 = x")
    case True
    then show ?thesis proof -
      have "length (extract_variables (map Inl (\<alpha> x y0))) \<le> card (UNIV::'y set) * k"
        by (simp, rule variable_count_in_bounded_shuffle[OF assms(2)])
      then have "length_scanned (scan (map Inl (\<alpha> x y0))) \<le> Suc (card (UNIV::'y set) * k)"
        by (simp add: length_scanned_of_variable_count)
      also have "Suc (card (UNIV::'y set) * k) = length (Enum.enum::('y::enum, 'k) type_mult_suc list)"
        using assms unfolding boundedness_def
        by (simp add: card_UNIV_length_enum[symmetric] card_cartesian_product[symmetric] card_UNIV_option)
      finally have *:"length_scanned (scan (map Inl (\<alpha> x y0))) \<le> length (Enum.enum::('y::enum, 'k) type_mult_suc list)" .
      show ?thesis
        by (simp add: \<iota>_def synthesize_def synthesize_shuffle_def comp_def True count_list_synthesize[OF *])
    qed
  next
    case False
    then show ?thesis proof -
      have w: "\<forall>yi\<in>set (\<iota> B \<alpha> x y0). pred_only_x_y x y0 yi"
        by (simp add: iota_x_y Ball_set_list_all)
      show ?thesis
        by (metis False count_notin le_SucI le_zero_eq pred_only_x_y_apply w)
    qed
  qed
  finally show "sum ?f UNIV \<le> Suc 0" .
qed


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


theorem convert_MSST_bounded:
  fixes msst :: "('q::finite, 'x::finite, 'y::enum, 'a, 'b) MSST"
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

end
