theory Bounded_Copy
  imports Main SST Finite_Set SingleUse
begin

definition trim :: "('q, 'x, 'a, 'b) SST \<Rightarrow> bool" where
  "trim sst \<equiv> (\<forall>q. \<exists>w. SST.delta_hat sst (SST.initial sst, w) = q)"

definition bounded_copy_SST :: "[ nat, ('q::finite, 'x::finite, 'a, 'b) SST ] \<Rightarrow> bool" where
  "bounded_copy_SST k sst \<equiv> (\<forall>w q. bounded k (SST.eta_hat sst (q, w)))"



end