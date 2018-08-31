theory Convert_Monoid_SST_Type_Misc
  imports Main 
          "../Core/Update" "../Core/SST" "../Core/Monoid_SST" "../Decomposition/Decompose_Update"
          "../Composition/Convert_Monoid_SST_Def"
          "../Type/Monoid_SST_Type"
begin

lemma resolve_shuffle_iota:
  "resolve_shuffle (\<iota> B \<alpha> x) = \<alpha> x"
  unfolding \<iota>_def
  by (simp add: synthesize_inverse_shuffle)

lemma iota_alpha_type_hom:
  assumes "\<forall>x. \<alpha> x \<in> \<gamma> (q, x)"
  shows "resolve_shuffle (hat_homU (\<iota> B \<alpha>) u) \<in> type_hom \<gamma> (q, u)"
proof (induct u rule: xa_induct)
  case Nil
  then show ?case by (simp add: resolve_idU_idS)
next
  case (Var x xs)
  then show ?case 
    by (simp add: resolve_shuffle_distrib mult_shuffles_member resolve_shuffle_iota assms)
next
  case (Alpha a xs)
  then show ?case 
    by (simp add: resolve_shuffle_distrib resolve_shuffle_map_alpha  mult_shuffles_member)
qed

lemma initial_condition_of_convert_MSST_state:
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  fixes \<gamma> :: "('q, 'x, 'y) msst_type"
  assumes assm_is_type: "is_type msst \<gamma>"
  shows "\<alpha>0 x \<in> \<gamma> (initial msst, x)"
  using assm_is_type unfolding is_type_def \<alpha>0_def by simp

lemma step_condition_of_convert_MSST_state:
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  fixes \<gamma> :: "('q, 'x, 'y) msst_type"
  assumes assm_is_type: "is_type msst \<gamma>"
  assumes assm_prev:    "\<forall>x. \<alpha>' x \<in> \<gamma> (q', x)"
  assumes assm_states:  "(q, \<alpha>) = delta (convert_MSST B msst) ((q', \<alpha>'), a)"
  shows "\<alpha> x \<in> \<gamma> (q, x)"
  using assm_states unfolding convert_MSST_def convert_\<delta>_def \<Delta>'_def
proof (simp)
  have q: "q = delta msst (q', a)"
    using assm_states unfolding convert_MSST_def convert_\<delta>_def by simp
  have "resolve_shuffle (hat_homU (\<iota> B \<alpha>') (SST.eta msst (q', a) x))
      \<in> type_hom \<gamma> (q', SST.eta msst (q', a) x)"
    by (simp add: iota_alpha_type_hom assm_prev)
  also have "... \<subseteq> \<gamma> (delta msst (q', a), x)"
    using assm_is_type unfolding is_type_def by simp
  finally show "resolve_shuffle (hat_homU (\<iota> B \<alpha>') (SST.eta msst (q', a) x))
              \<in> \<gamma> (delta msst (q', a), x)" .
qed

lemma condition_of_convert_MSST_state:
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  fixes \<gamma> :: "('q, 'x, 'y) msst_type"
  assumes assm_is_type: "is_type msst \<gamma>"
  assumes assm_states:  "(q, \<alpha>) = delta_hat (convert_MSST B msst) (initial (convert_MSST B msst), w)"
  shows "\<alpha> x \<in> \<gamma> (q, x)"
using assm_states proof (induct w arbitrary: q \<alpha> x rule: rev_induct)
case Nil
  then show ?case
    unfolding convert_MSST_def by (simp add: initial_condition_of_convert_MSST_state assms)
next
  case (snoc a w)
  show ?case proof (rule step_condition_of_convert_MSST_state)
    let ?st = "delta_hat (convert_MSST B msst) (initial (convert_MSST B msst), w)"
    show "is_type msst \<gamma>" using assm_is_type by simp
    show "\<forall>x. (snd ?st) x \<in> \<gamma> (fst ?st, x)"
      by (rule allI, rule snoc(1), simp)
    show "(q, \<alpha>) = delta (convert_MSST B msst) ((fst ?st, snd ?st), a)"
      by (simp add: snoc.prems)
  qed
qed

lemma condition_of_convert_MSST_reachable_state:
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  fixes \<gamma> :: "('q, 'x, 'y) msst_type"
  fixes B :: "'k::enum boundedness"
  assumes assm_is_type: "is_type msst \<gamma>"
  assumes assm_states:  "(q, \<alpha>) = delta_hat (convert_MSST B msst) (initial (convert_MSST B msst), w)"
  assumes assm_reachable: "reachable (convert_MSST B msst) (q, \<alpha>)"
  shows "\<alpha> x \<in> \<gamma> (q, x)"
  by (meson assm_is_type assm_states condition_of_convert_MSST_state)

lemma hat_homU_iota_bounded_copy:
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  fixes \<gamma> :: "('q, 'x, 'y) msst_type"
  fixes B :: "'k::enum boundedness"
  assumes assm_k_bounded: "boundedness B k"
  assumes assm_is_type: "is_type msst \<gamma>"
  assumes assm_bounded_type: "bounded_copy_type k msst \<gamma>"
  assumes assm_reachable: "reachable (convert_MSST B msst) (q, \<alpha>)"
  shows "bounded k (hat_homU (\<iota> B \<alpha>) (SST.eta_hat msst (q, w) x))"
proof -
  have "resolve_shuffle (hat_homU (\<iota> B \<alpha>) (SST.eta_hat msst (q, w) x)) \<in> type_hom \<gamma> (q, (SST.eta_hat msst (q, w) x))"
    by (meson assm_is_type assm_reachable condition_of_convert_MSST_state iota_alpha_type_hom reachable_def)
  also have "... \<subseteq> \<gamma> (delta_hat msst (q, w), x)" by (simp add: type_hom_hat assm_is_type)
  finally have in_type: "resolve_shuffle (hat_homU (\<iota> B \<alpha>) (SST.eta_hat msst (q, w) x)) \<in> \<gamma> (delta_hat msst (q, w), x)" .
  have "reachable msst (delta_hat msst (q, w))" proof (rule reachable_delta_hat)
    show "reachable msst q" using assm_reachable unfolding convert_MSST_def reachable_def by (auto simp add: convert_\<delta>_hat)
  qed
  then have "bounded_shuffle k (resolve_shuffle (hat_homU (\<iota> B \<alpha>) (SST.eta_hat msst (q, w) x)))"
    using assm_bounded_type in_type unfolding bounded_copy_type_def by auto
  then show ?thesis by (rule resolve_bounded_inverse)
qed


end
