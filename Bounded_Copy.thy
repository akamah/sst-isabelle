theory Bounded_Copy
  imports Main SST Finite_Set SingleUse Decompose_Update
begin


definition reachable :: "('q, 'x, 'a, 'b) SST \<Rightarrow> 'q \<Rightarrow> bool" where
  "reachable sst q \<equiv> (\<exists>w. q = SST.delta_hat sst (SST.initial sst, w))"

definition trim :: "('q, 'x, 'a, 'b) SST \<Rightarrow> bool" where
  "trim sst \<equiv> \<forall>q. reachable sst q"

definition bounded_copy_SST :: "[ nat, ('q::finite, 'x::finite, 'a, 'b) SST ] \<Rightarrow> bool" where
  "bounded_copy_SST k sst \<equiv> (\<forall>w q. reachable sst q \<longrightarrow> bounded k (SST.eta_hat sst (q, w)))"



end