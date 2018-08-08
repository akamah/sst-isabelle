(* Title:   Monoid_SST_Type.thy
   Author:  Akama Hitoshi
*)


theory Monoid_SST_Type
  imports Main "../Core/Update" "../Core/Monoid_SST" "../Decomposition/Decompose_Update"
begin

type_synonym ('q, 'x, 'y) msst_type = "'q \<times> 'x \<Rightarrow> 'y shuffle set"


lemma concat_map_right_idS [simp]: "concat o map a o idS = a"
  by (rule ext, simp add: idS_def)

lemma concat_map_left_idS [simp]: "concat o map idS o a = a"
  by (rule ext, simp add: idS_def)

lemma concat_map_assoc: "concat o map a o (concat o map b o c) = concat o map (concat o map a o b) o c"
proof -
  { fix l
    have "concat (map (concat o map a o b) l)
        = concat (map a (concat (map b l)))" by (induct l, simp_all)
  } note that = this
  show ?thesis by (rule ext, simp add: that)
qed

definition mult_shuffles where
  "mult_shuffles A B = (\<Union>a\<in>A. \<Union>b\<in>B. { concat \<circ> map a \<circ> b })"

lemma mult_shuffles_right_unit [simp]: "mult_shuffles A { idS } = A"
  by (simp add: mult_shuffles_def)

lemma mult_shuffles_left_unit [simp]: "mult_shuffles { idS } A = A"
  by (simp add: mult_shuffles_def)

lemma mult_shuffles_assoc [simp]:
  "mult_shuffles A (mult_shuffles B C) = mult_shuffles (mult_shuffles A B) C" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs" by (simp add: mult_shuffles_def concat_map_assoc)
next
  show "?rhs \<subseteq> ?lhs" by (simp add: mult_shuffles_def concat_map_assoc)
qed

lemma mult_shuffles_subset:
  assumes "A \<subseteq> C"
  assumes "B \<subseteq> D"
  shows "mult_shuffles A B \<subseteq> mult_shuffles C D"
proof
  fix x
  assume "x \<in> mult_shuffles A B"
  then show "x \<in> mult_shuffles C D" proof -
    obtain a b where ab: "x = concat o map a o b \<and> a \<in> A \<and> b \<in> B"
      by (metis (no_types, lifting) UN_E \<open>x \<in> mult_shuffles A B\<close> mult_shuffles_def singletonD)
    then have cd: "a \<in> C \<and> b \<in> D" using assms(1) assms(2) by blast
    then show ?thesis
      apply (simp add: mult_shuffles_def ab) using cd by blast
  qed
qed

lemma mult_shuffles_member:
  assumes "a \<in> A"
  assumes "b \<in> B"
  shows "(\<lambda>x. concat (map a (b x))) \<in> mult_shuffles A B"
  unfolding mult_shuffles_def
proof (simp, intro bexI)
  show "(\<lambda>x. concat (map a (b x))) = concat o map a o b" by (rule ext, simp)
next
  show "b \<in> B" using assms by simp
next
  show "a \<in> A" using assms by simp
qed


fun type_hom :: "('q, 'x, 'y) msst_type \<Rightarrow> ('q \<times> (('x + ('y, 'b) update) list) \<Rightarrow> 'y shuffle set)" where
  "type_hom \<gamma> (q, []) = { idS }" |
  "type_hom \<gamma> (q, (Inl x#xs)) = mult_shuffles (\<gamma> (q, x)) (type_hom \<gamma> (q, xs))" |
  "type_hom \<gamma> (q, (Inr m#xs)) = mult_shuffles { resolve_shuffle m } (type_hom \<gamma> (q, xs))"

definition is_type :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow> ('q, 'x, 'y) msst_type \<Rightarrow> bool" where
  "is_type msst \<gamma> \<equiv> (\<forall>x. idS \<in> \<gamma> (initial msst, x)) \<and>
                     (\<forall>x q a. type_hom \<gamma> (q, eta msst (q, a) x) \<subseteq> \<gamma> (delta msst (q, a), x))"


lemma type_hom_append [simp]: "type_hom \<gamma> (q, u @ v) = mult_shuffles (type_hom \<gamma> (q, u)) (type_hom \<gamma> (q, v))"
  by (induct u arbitrary: q rule: xa_induct, simp_all)

lemma type_hom_subset:
  assumes "is_type msst \<gamma>"
  shows "type_hom \<gamma> (q, hat_hom (SST.eta msst (q, a)) u) 
      \<subseteq> type_hom \<gamma> (delta msst (q, a), u)"
proof (induct u rule: xa_induct)
case Nil
  then show ?case by simp
next
  case (Var x xs)
  show ?case
    apply (simp)
    apply (rule mult_shuffles_subset)
    using assms apply (simp_all add: is_type_def Var)
    done
next
  case (Alpha a xs)
  then show ?case
    apply (simp)
    apply (rule mult_shuffles_subset)
    using assms apply (simp_all add: is_type_def Alpha)
    done
qed

lemma
  assumes "is_type msst \<gamma>"
  shows "type_hom \<gamma> (q, hat_hom (eta_hat msst (q, w)) u)
      \<subseteq> type_hom \<gamma> (delta_hat msst (q, w), u)"
proof (induct w arbitrary: q u)
case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case proof (simp add: comp_def comp_lem[symmetric] del: Fun.comp_apply)
    let ?q' = "delta msst (q, a)"
    let ?e' = "SST.eta msst (q, a)"
    let ?uu = "hat_hom (SST.eta_hat msst (?q', w)) u"
    have "type_hom \<gamma> (q, hat_hom ?e' ?uu) \<subseteq> type_hom \<gamma> (?q', ?uu)" using assms by (simp add: type_hom_subset)
    also have "... \<subseteq> type_hom \<gamma> (delta_hat msst (?q', w), u)" by (simp add: Cons)
    finally show "type_hom \<gamma> (q, hat_hom ?e' ?uu) \<subseteq> type_hom \<gamma> (delta_hat msst (?q', w), u)" .
  qed    
qed

definition bounded_copy_type :: "nat \<Rightarrow> ('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow> ('q, 'x, 'y) msst_type \<Rightarrow> bool" where
  "bounded_copy_type k msst \<gamma> \<equiv> (\<forall>q x. \<forall>m \<in> \<gamma> (q, x). (reachable msst q \<longrightarrow> bounded_shuffle k m))"

end
