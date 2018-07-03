theory Bounded_Copy
  imports Main SST Finite_Set
begin

definition trim :: "('q, 'x, 'a, 'b) SST \<Rightarrow> bool" where
  "trim sst \<equiv> (\<forall>q. \<exists>w. SST.delta_hat sst (SST.initial sst, w) = q)"


end