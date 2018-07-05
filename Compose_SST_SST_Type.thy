theory Compose_SST_SST_Type 
  imports Compose_SST_SST Decompose_Update Monoid_SST_Type
begin


definition compose_\<gamma>_pred where
  "compose_\<gamma>_pred sst2 f q2 x m1 =
    (\<exists>m w. SST.delta_hat sst2 (q2, w) = f (q2, x) \<and>
           SST.eta_hat sst2 (q2, w) = m \<and>
           m1 = resolve_shuffle m)"

definition compose_\<gamma> ::
  "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'x2, 'b, 'c) SST \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'x2) msst_type" where
   "compose_\<gamma> sst1 sst2 = (\<lambda>((q1, f), (q2, x)).
      { m1. compose_\<gamma>_pred sst2 f q2 x m1 })"

lemma compose_\<gamma>_simp:
  "compose_\<gamma> sst1 sst2 ((q1, f), (q2, x)) = { m1. compose_\<gamma>_pred sst2 f q2 x m1 }"
  unfolding compose_\<gamma>_def by simp

lemma compose_\<gamma>_subset:
  "type_hom (compose_\<gamma> sst1 sst2)
     ((q1, f), Transducer.hat2 (delta2f f (SST.delta sst2)) (eta2f (SST.eta sst2))
                 (q2, u))
   \<subseteq> {m1. \<exists>w. SST.delta_hat sst2 (q2, w) = SST.hat1 (delta2f f (SST.delta sst2)) (q2, u) \<and>
              m1 = resolve_shuffle (SST.eta_hat sst2 (q2, w))}"
proof (induct u arbitrary: q2 rule: xa_induct)
  case Nil
  then show ?case by (simp, metis SST.hat1.simps(1) SST.hat2.simps(1) resolve_idU_idS)
next
  case (Var x xs)
  then show ?case apply (simp add: compose_\<gamma>_simp) sorry
next
  case (Alpha a xs)
  then show ?case sorry
qed


lemma "is_type (compose_SST_SST sst1 sst2) (compose_\<gamma> sst1 sst2)"
  unfolding is_type_def
proof
  show "(\<forall>x. idS \<in> compose_\<gamma> sst1 sst2 (MSST.initial (compose_SST_SST sst1 sst2), x))"
    unfolding compose_SST_SST_def
    apply (simp add: compose_\<gamma>_def compose_\<gamma>_pred_def)
    apply (metis SST.hat1.simps(1) SST.hat2.simps(1) resolve_idU_idS)
    done
next
  show "\<forall>x q a. type_hom (compose_\<gamma> sst1 sst2) (q, MSST.eta (compose_SST_SST sst1 sst2) (q, a) x)
                \<subseteq> compose_\<gamma> sst1 sst2 (MSST.delta (compose_SST_SST sst1 sst2) (q, a), x)"
    apply (simp add: compose_\<gamma>_simp compose_SST_SST_def compose_\<delta>_def \<Delta>_def compose_\<eta>_def H_def)
    apply (simp add: compose_\<gamma>_pred_def)
    apply (simp add: compose_\<gamma>_subset)
    done
qed


end
