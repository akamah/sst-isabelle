(* Title:   Monoid_SST_Type.thy
   Author:  Akama Hitoshi
*)


theory Monoid_SST_Type
  imports Main "../Core/Update" "../Core/Monoid_SST" "../Decomposition/Shuffle"
begin

type_synonym ('q, 'x, 'y) msst_type = "'q \<times> 'x \<Rightarrow> 'y shuffle set"


definition mult_shuffles :: "'x shuffle set \<Rightarrow> 'x shuffle set \<Rightarrow> 'x shuffle set" (infixl "\<otimes>" 60) where
  "A \<otimes> B = (\<Union>a\<in>A. \<Union>b\<in>B. { a \<odot> b })"

lemma mult_shuffles_member:
  assumes a: "a \<in> A"
  assumes b: "b \<in> B"
  shows "a \<odot> b \<in> A \<otimes> B"
  using a b by (auto simp add: mult_shuffles_def)

lemma mult_shuffles_right_unit [simp]: "A \<otimes> { idS } = A"
  by (simp add: mult_shuffles_def)

lemma mult_shuffles_left_unit [simp]: "{ idS } \<otimes> A = A"
  by (simp add: mult_shuffles_def)

lemma mult_shuffles_assoc [simp]:
  "A \<otimes> (B \<otimes> C) = (A \<otimes> B) \<otimes> C"
  by (rule equalityI, simp_all add: mult_shuffles_def compS_assoc)

lemma mult_shuffles_subset:
  assumes "A \<subseteq> C"
  assumes "B \<subseteq> D"
  shows "A \<otimes> B \<subseteq> C \<otimes> D"
proof
  fix x
  assume "x \<in> A \<otimes> B"
  then obtain a b where ab: "x = a \<odot> b \<and> a \<in> A \<and> b \<in> B"
    unfolding mult_shuffles_def by blast
  then have cd: "a \<in> C \<and> b \<in> D" using assms(1) assms(2) by blast
  then show "x \<in> C \<otimes> D" by (auto simp add: mult_shuffles_member ab)
qed


definition tails where
  "tails xs = {ys. \<exists>zs. xs = zs @ ys}"

fun type_hom :: "('q, 'x, 'y) msst_type \<Rightarrow> ('q \<times> (('x + ('y, 'b) update) list) \<Rightarrow> 'y shuffle set)" where
  "type_hom \<gamma> (q, []) = { idS }" |
  "type_hom \<gamma> (q, (Inl x#xs)) = \<gamma> (q, x) \<otimes> type_hom \<gamma> (q, xs)" |
  "type_hom \<gamma> (q, (Inr m#xs)) = { \<pi>\<^sub>1 m } \<otimes> type_hom \<gamma> (q, xs)"


definition bctype_idS where
  "bctype_idS k msst \<gamma> = (\<forall>x. idS \<in> \<gamma> (initial msst, x))"

definition bctype_step where
  "bctype_step k msst \<gamma> = (\<forall>x q a. type_hom \<gamma> (q, eta msst (q, a) x) \<subseteq> \<gamma> (delta msst (q, a), x))"

definition bctype_bounded where
  "bctype_bounded k msst \<gamma> = (\<forall>q x. \<forall>m \<in> \<gamma> (q, x). (reachable msst q \<longrightarrow> bounded_shuffle k m))"

definition bctype_tails where
  "bctype_tails k msst \<gamma> = (\<forall>q x w. \<forall>u \<in> tails (SST.eta_hat msst (q, w) x). 
        \<forall>m \<in> type_hom \<gamma> (q, u). (reachable msst q \<longrightarrow> bounded_shuffle k m))"


definition bctype :: "nat \<Rightarrow> ('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow> ('q, 'x, 'y) msst_type \<Rightarrow> bool" where
  "bctype k msst \<gamma> \<equiv> bctype_idS k msst \<gamma> \<and> bctype_step k msst \<gamma> \<and>
                      bctype_bounded k msst \<gamma> \<and> bctype_tails k msst \<gamma>"

lemma bctype_idS:
  assumes "bctype k msst \<gamma>"
  shows "idS \<in> \<gamma> (initial msst, x)"
  using assms unfolding bctype_def bctype_idS_def by simp

lemma bctype_step:
  assumes "bctype k msst \<gamma>"
  shows "type_hom \<gamma> (q, eta msst (q, a) x) \<subseteq> \<gamma> (delta msst (q, a), x)"
  using assms unfolding bctype_def bctype_step_def by simp

lemma bctype_bounded:
  assumes "bctype k msst \<gamma>"
  assumes "reachable msst q"
  assumes "m \<in> \<gamma> (q, x)"
  shows "bounded_shuffle k m"
  using assms unfolding bctype_def bctype_bounded_def by simp

lemma bctype_tails:
  assumes "bctype k msst \<gamma>"
  assumes "reachable msst q"
  assumes "u \<in> tails (SST.eta_hat msst (q, w) x)"
  assumes "m \<in> type_hom \<gamma> (q, u)"
  shows "bounded_shuffle k m"
  using assms unfolding bctype_def bctype_tails_def by simp


lemma type_hom_append [simp]: "type_hom \<gamma> (q, u @ v) = type_hom \<gamma> (q, u) \<otimes> type_hom \<gamma> (q, v)"
  by (induct u arbitrary: q rule: xa_induct, simp_all)

lemma type_hom_subset:
  assumes bc: "bctype k msst \<gamma>"
  shows "type_hom \<gamma> (q, hat_hom (SST.eta msst (q, a)) u) 
      \<subseteq> type_hom \<gamma> (delta msst (q, a), u)"
  using bctype_step[OF bc]
  by (induct u rule: xa_induct, simp_all add: mult_shuffles_subset)


lemma type_hom_hat_hom:
  assumes "bctype k msst \<gamma>"
  shows "type_hom \<gamma> (q, hat_hom (eta_hat msst (q, w)) u)
      \<subseteq> type_hom \<gamma> (delta_hat msst (q, w), u)"
proof (induct w arbitrary: q u)
case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case (is "?a \<subseteq> ?b") proof -
    have "?a \<subseteq> type_hom \<gamma> (delta msst (q, a), hat_hom (SST.eta_hat msst (delta msst (q, a), w)) u)"
      using assms by (simp add: type_hom_subset compU_lem)
    also have "... \<subseteq> ?b"
      by (simp add: Cons)
    finally show "?a \<subseteq> ?b" .
  qed    
qed


end
