theory State_Machine
  imports Main
begin


section \<open>Definitions\<close>

text \<open>Transition function\<close>
type_synonym ('q, 'a) trans = 
  "'q \<times> 'a \<Rightarrow> 'q"

text \<open>simple state-machine\<close>
record ('q, 'a) state_machine =
  states :: "'q set"
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

definition closed_delta :: "['q set, ('q, 'a) trans] \<Rightarrow> bool" where
  "closed_delta st tr \<equiv> \<forall>q\<in>st. \<forall>a. tr (q, a) \<in> st"

definition st_well_defined :: "('q, 'a, 'e) state_machine_scheme \<Rightarrow> bool" where
  "st_well_defined m \<equiv> initial_in_states (states m) (initial m)
                      \<and> closed_delta (states m) (delta m)"

lemmas st_well_defined_simps =
  st_well_defined_def initial_in_states_def closed_delta_def


definition reachable :: "('q, 'a, 'e) state_machine_scheme \<Rightarrow> 'q \<Rightarrow> bool" where
  "reachable m q \<equiv> (\<exists>w. q = delta_hat m (initial m, w))"

definition trim :: "('q, 'a, 'e) state_machine_scheme \<Rightarrow> bool" where
  "trim m \<equiv> \<forall>q. reachable m q"

section \<open>Properties\<close>

lemma closed_delta_hat_iff_closed_delta[iff]:
  "closed_delta st (hat1 tr) \<longleftrightarrow> closed_delta st tr"
proof
  assume 0: "closed_delta st (hat1 tr)"
  show "closed_delta st tr"
    unfolding closed_delta_def
  proof (rule ballI, rule allI)
    fix q a
    assume q: "q \<in> st"
    have "hat1 tr (q, [a]) \<in> st"
      using 0 unfolding closed_delta_def
      by (simp add: 0 q del: hat1.simps)
    then show "tr (q, a) \<in> st" by simp
  qed
next
  assume 0: "closed_delta st tr"
  show "closed_delta st (hat1 tr)"
    unfolding closed_delta_def
  proof (rule ballI, rule allI)
    fix q w
    assume q: "q \<in> st"
    { fix q w
      have "q \<in> st \<Longrightarrow> hat1 tr (q, w) \<in> st"
        using 0 unfolding closed_delta_def
        by (induct w arbitrary: q, simp_all)
    }
    then show "hat1 tr (q, w) \<in> st" using q by simp
  qed
qed


lemma delta_append[simp]:
  "hat1 t (q, u @ v) = hat1 t (hat1 t (q, u), v)"
  by (induct u arbitrary: q, auto)


end
