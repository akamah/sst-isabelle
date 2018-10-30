theory State_Machine
  imports Main
begin


section \<open>Definitions\<close>

text \<open>Transition function\<close>
type_synonym ('q, 'a) trans = 
  "'q \<times> 'a \<Rightarrow> 'q"

text \<open>simple state-machine\<close>
record ('q, 'a) state_machine =
  initial :: "'q"
  delta :: "('q, 'a) trans"

text \<open>closure of transition function\<close>
fun hat1 :: "('q, 'a) trans \<Rightarrow> ('q, 'a list) trans" where
  "hat1 t (q, [])     = q" |
  "hat1 t (q, (a#as)) = hat1 t (t (q, a), as)"

abbreviation delta_hat ::
  "('q, 'a, 'e) state_machine_scheme \<Rightarrow> ('q, 'a list) trans" where
  "delta_hat m \<equiv> hat1 (delta m)"

definition initial_in_states :: "['q set, 'q] \<Rightarrow> bool" where
  "initial_in_states st q0 \<equiv> q0 \<in> st"

definition reachable :: "('q, 'a, 'e) state_machine_scheme \<Rightarrow> 'q \<Rightarrow> bool" where
  "reachable m q \<equiv> (\<exists>w. q = delta_hat m (initial m, w))"

definition trim :: "('q, 'a, 'e) state_machine_scheme \<Rightarrow> bool" where
  "trim m \<equiv> \<forall>q. reachable m q"

section \<open>Properties\<close>

lemma delta_append[simp]:
  "hat1 t (q, u @ v) = hat1 t (hat1 t (q, u), v)"
  by (induct u arbitrary: q, auto)

lemma delta_append_1:
  "hat1 t (q, u @ [a]) = t (hat1 t (q, u), a)"
  by (induct u rule: rev_induct, simp_all)

lemma reachable_initial:
  "reachable m (initial m)"
  unfolding reachable_def
  by (metis hat1.simps(1))

lemma reachable_delta:
  assumes "reachable m q"
  shows "reachable m (delta m (q, a))"
  by (metis assms delta_append_1 reachable_def)

lemma reachable_delta_hat:
  assumes "reachable m q"
  shows "reachable m (delta_hat m (q, w))"
  by (metis assms delta_append reachable_def)

end
