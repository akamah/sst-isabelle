theory Bounded_Copy_Convert
  imports Main Finite_Set
          "../Util/Enum_Nat" "../Core/Update" "../Single_Use/Single_Use" "../Decomposition/Decompose_Update"
begin


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

end
