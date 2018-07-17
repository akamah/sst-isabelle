theory Bounded_Copy
  imports Main SST Finite_Set SingleUse Decompose_Update
begin



definition bounded_copy_SST :: "[ nat, ('q::finite, 'x::finite, 'a, 'b) SST ] \<Rightarrow> bool" where
  "bounded_copy_SST k sst \<equiv> (\<forall>w q. reachable sst q \<longrightarrow> bounded k (SST.eta_hat sst (q, w)))"



end