theory Bounded_Copy
  imports Main Finite_Set "../Core/SST" SingleUse
begin



definition bounded_copy_SST :: "[ nat, ('q::finite, 'x::finite, 'a, 'b) SST ] \<Rightarrow> bool" where
  "bounded_copy_SST k sst \<equiv> (\<forall>w q. reachable sst q \<longrightarrow> bounded k (SST.eta_hat sst (q, w)))"

lemma bounded_copy_SST_simp:
  assumes "bounded_copy_SST k sst" and "reachable sst q"
  shows "bounded k (SST.eta_hat sst (q, w))"
  using assms unfolding bounded_copy_SST_def by simp


end