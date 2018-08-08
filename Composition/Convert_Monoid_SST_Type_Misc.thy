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

lemma condition_of_convert_MSST_state:
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  fixes \<gamma> :: "('q, 'x, 'y) msst_type"
  assumes assm_is_type: "is_type msst \<gamma>"
  assumes assm_states:  "(q, \<alpha>) = delta_hat (convert_MSST B msst) (initial (convert_MSST B msst), w)"
  shows "\<alpha> x \<in> \<gamma> (q, x)"
using assm_states proof (induct w arbitrary: q \<alpha> x rule: rev_induct)
case Nil
  then show ?case
    using assm_is_type unfolding convert_MSST_def \<alpha>0_def is_type_def by simp
next
  case (snoc a w)
  let ?q'= "delta_hat msst (initial msst, w)"
  let ?\<alpha>' = "\<Delta>' B (\<alpha>0, SST.eta_hat msst (initial msst, w))"
  have IH_alpha: "\<forall>x'. ?\<alpha>' x' \<in> \<gamma> (?q', x')"
    using snoc unfolding convert_MSST_def by (simp add: convert_\<delta>_hat)
  have qa: "(q, \<alpha>) = delta (convert_MSST B msst) ((?q', ?\<alpha>'), a)"
    using snoc.prems unfolding convert_MSST_def by (simp add: convert_\<delta>_hat)
  have q: "q = delta msst (?q', a)" 
    using qa unfolding convert_MSST_def convert_\<delta>_def by simp
  then have \<alpha>: "\<alpha> = \<Delta>' B (?\<alpha>', SST.eta msst (?q', a)) "
    using qa unfolding convert_MSST_def convert_\<delta>_def by simp
  then have "\<alpha> x = \<Delta>' B (?\<alpha>', SST.eta msst (?q', a)) x"
    unfolding convert_MSST_def convert_\<delta>_def by simp
  also have "... = resolve_shuffle (hat_homU (\<iota> B ?\<alpha>') (SST.eta msst (?q', a) x))"
    unfolding \<Delta>'_def by simp
  also have "... \<in> type_hom \<gamma> (?q', SST.eta msst (?q', a) x)"
    by (simp add: iota_alpha_type_hom IH_alpha)
  also have "... \<subseteq> \<gamma> (q, x)"
    using assm_is_type unfolding is_type_def by (simp add: q \<alpha>)
  finally show ?case .
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
