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
  fixes B :: "'k::enum boundedness"
  assumes assm_is_type: "is_type msst \<gamma>"
  assumes assm_boundedness: "boundedness B k"
  assumes assm_bounded_type: "bounded_copy_type k msst \<gamma>"
  assumes assm_prev:    "\<forall>x. Rep_alpha B \<beta>' x \<in> \<gamma> (q', x)"
  assumes assm_reachable: "reachable (convert_MSST B msst) (q', \<beta>')"
  assumes assm_states:  "(q, \<beta>) = delta (convert_MSST B msst) ((q', \<beta>'), a)"
  shows "Rep_alpha B \<beta> x \<in> \<gamma> (q, x)"
  using assm_states unfolding convert_MSST_def convert_\<delta>_def \<Delta>'_def
proof (simp)
  have q: "q = delta msst (q', a)"
    using assm_states unfolding convert_MSST_def convert_\<delta>_def by simp
  let ?hhU = "hat_homU (\<iota> B (Rep_alpha B \<beta>')) (SST.eta msst (q', a) x)"
  have "resolve_shuffle ?hhU \<in> type_hom \<gamma> (q', SST.eta msst (q', a) x)"
    by (rule iota_alpha_type_hom, rule assm_prev)
  also have "... \<subseteq> \<gamma> (delta msst (q', a), x)"
    using assm_is_type unfolding is_type_def by simp
  finally have hhU_typed: "resolve_shuffle ?hhU \<in> \<gamma> (delta msst (q', a), x)" .
  have "reachable msst (delta msst (q', a))" proof -
    have "reachable msst q'" using assm_reachable 
      by (rule reachable_convert)
    then show ?thesis by (rule reachable_delta)
  qed
  then have hhU_bc: "bounded_shuffle k (resolve_shuffle ?hhU)"
    using assm_bounded_type hhU_typed unfolding bounded_copy_type_def
    by auto
  have "Rep_bc_shuffle (Abs_bc_shuffle (resolve_shuffle ?hhU) :: ('k, 'y) bc_shuffle)
     = resolve_shuffle ?hhU"
    using assm_boundedness hhU_bc
    unfolding boundedness_def
    by (auto simp add: Abs_bc_shuffle_inverse)
  also have "... \<in> type_hom \<gamma> (q', SST.eta msst (q', a) x)"
    by (rule iota_alpha_type_hom, rule assm_prev)
  also have "... \<subseteq> \<gamma> (delta msst (q', a), x)"
    using assm_is_type unfolding is_type_def by simp
  finally show "Rep_bc_shuffle (Abs_bc_shuffle (resolve_shuffle ?hhU) :: ('k, 'y) bc_shuffle)
              \<in> \<gamma> (delta msst (q', a), x)" .
qed

lemma condition_of_convert_MSST_state:
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  fixes \<gamma> :: "('q, 'x, 'y) msst_type"
  fixes B :: "'k::enum boundedness"
  assumes assm_bounded: "boundedness B k"
  assumes assm_is_type: "is_type msst \<gamma>"
  assumes assm_bc_type: "bounded_copy_type k msst \<gamma>"
  assumes assm_states:  "(q, \<beta>) = delta_hat (convert_MSST B msst) (initial (convert_MSST B msst), w)"
  shows "Rep_alpha B \<beta> x \<in> \<gamma> (q, x)"
using assm_states proof (induct w arbitrary: q \<beta> x rule: rev_induct)
case Nil
  then show ?case
    using assms unfolding convert_MSST_def bounded_copy_type_def reachable_def
  proof (simp add: assms idS_bounded del: Rep_alpha.simps Abs_alpha.simps)
    show "\<alpha>0 x \<in> \<gamma> (initial msst, x)"
      using assm_is_type unfolding is_type_def \<alpha>0_def by simp
  qed
next
  case (snoc a w)
  show ?case proof (rule step_condition_of_convert_MSST_state)
    let ?st = "delta_hat (convert_MSST B msst) (initial (convert_MSST B msst), w)"
    show "is_type msst \<gamma>" using assm_is_type by simp
    show "boundedness B k" using assm_bounded by simp
    show "bounded_copy_type k msst \<gamma>" using assm_bc_type by simp
    show "\<forall>x. Rep_alpha B (snd ?st) x \<in> \<gamma> (fst ?st, x)"
      by (rule allI, rule snoc(1), simp)
    show "(q, \<beta>) = delta (convert_MSST B msst) ((fst ?st, snd ?st), a)"
      by (simp add: snoc.prems)
    show "reachable (convert_MSST B msst) (fst ?st, snd ?st)"
      by (auto simp add: reachable_def)
  qed
qed

lemma condition_of_convert_MSST_reachable_state:
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  fixes \<gamma> :: "('q, 'x, 'y) msst_type"
  fixes B :: "'k::enum boundedness"
  assumes assm_bounded: "boundedness B k"
  assumes assm_is_type: "is_type msst \<gamma>"
  assumes assm_bc_type: "bounded_copy_type k msst \<gamma>"
  assumes assm_reachable:  "reachable (convert_MSST B msst) (q, \<beta>)"
  shows "Rep_alpha B \<beta> x \<in> \<gamma> (q, x)"
  by (meson assm_bc_type assm_bounded assm_is_type assm_reachable condition_of_convert_MSST_state reachable_def)

lemma hat_homU_iota_bounded_copy:
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  fixes \<gamma> :: "('q, 'x, 'y) msst_type"
  fixes B :: "'k::enum boundedness"
  assumes assm_k_bounded: "boundedness B k"
  assumes assm_is_type: "is_type msst \<gamma>"
  assumes assm_bounded_type: "bounded_copy_type k msst \<gamma>"
  assumes assm_reachable: "reachable (convert_MSST B msst) (q, \<beta>)"
  shows "bounded k (hat_homU (\<iota> B (Rep_alpha B \<beta>)) (SST.eta_hat msst (q, w) x))"
proof -
  have "resolve_shuffle (hat_homU (\<iota> B (Rep_alpha B \<beta>)) (SST.eta_hat msst (q, w) x)) 
      \<in> type_hom \<gamma> (q, (SST.eta_hat msst (q, w) x))"
    by (meson assm_bounded_type assm_is_type assm_k_bounded assm_reachable condition_of_convert_MSST_reachable_state iota_alpha_type_hom)
  also have "... \<subseteq> \<gamma> (delta_hat msst (q, w), x)" by (simp add: type_hom_hat assm_is_type)
  finally have in_type: "resolve_shuffle (hat_homU (\<iota> B (Rep_alpha B \<beta>)) (SST.eta_hat msst (q, w) x)) 
               \<in> \<gamma> (delta_hat msst (q, w), x)" .
  have "reachable msst (delta_hat msst (q, w))"
    by (rule reachable_delta_hat, rule reachable_convert, rule assm_reachable)
  then have "bounded_shuffle k (resolve_shuffle (hat_homU (\<iota> B (Rep_alpha B \<beta>)) (SST.eta_hat msst (q, w) x)))"
    using assm_bounded_type in_type unfolding bounded_copy_type_def by auto
  then show ?thesis by (rule resolve_bounded_inverse)
qed

lemma hat_homU_iota_bounded_copy_tail:
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  fixes \<gamma> :: "('q, 'x, 'y) msst_type"
  fixes B :: "'k::enum boundedness"
  assumes assm_k_bounded: "boundedness B k"
  assumes assm_is_type: "is_type msst \<gamma>"
  assumes assm_bounded_type: "bounded_copy_type k msst \<gamma>"
  assumes assm_reachable: "reachable (convert_MSST B msst) (q, \<beta>)"
  assumes assm_tail: "u \<in> tails (SST.eta_hat msst (q, w) x)"
  shows "bounded k (hat_homU (\<iota> B (Rep_alpha B \<beta>)) u)"
proof -
  have reach: "reachable msst q" by (rule reachable_convert[OF assm_reachable])
  then have tail: "\<forall>m\<in>type_hom \<gamma> (q, u). bounded_shuffle k m"
    using assm_bounded_type assm_tail unfolding bounded_copy_type_def by auto
  then have "resolve_shuffle (hat_homU (\<iota> B (Rep_alpha B \<beta>)) u) 
      \<in> type_hom \<gamma> (q, u)"
    by (meson assm_bounded_type assm_is_type assm_k_bounded assm_reachable condition_of_convert_MSST_reachable_state iota_alpha_type_hom)
  then have "bounded_shuffle k (resolve_shuffle (hat_homU (\<iota> B (Rep_alpha B \<beta>)) u))"
    using assm_bounded_type assm_tail reach tail unfolding bounded_copy_type_def by auto
  then show "bounded k (hat_homU (\<iota> B (Rep_alpha B \<beta>)) u)"
    by (simp add: resolve_bounded_inverse)
qed

lemma resolve_shuffle_hat_homU_inverse:
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  fixes \<gamma> :: "('q, 'x, 'y) msst_type"
  fixes B :: "'k::enum boundedness"
  assumes assm_k_bounded: "boundedness B k"
  assumes assm_is_type: "is_type msst \<gamma>"
  assumes assm_bounded_type: "bounded_copy_type k msst \<gamma>"
  assumes assm_reachable: "reachable (convert_MSST B msst) (q, \<beta>)"
  shows "Rep_bc_shuffle (Abs_bc_shuffle
          (resolve_shuffle (hat_homU (\<iota> B (Rep_alpha B \<beta>)) (SST.eta_hat msst (q, w) x))) :: ('k, 'y) bc_shuffle)
       = resolve_shuffle (hat_homU (\<iota> B (Rep_alpha B \<beta>)) (SST.eta_hat msst (q, w) x))"
  apply (rule Abs_bc_shuffle_inverse, simp)
  apply (subst assm_k_bounded[simplified boundedness_def, symmetric])
  apply (rule resolve_bounded)
  apply (rule hat_homU_iota_bounded_copy)
     apply (rule assms)+
  done
end
