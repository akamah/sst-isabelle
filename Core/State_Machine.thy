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

definition closed_delta :: "['q set, 'a set, ('q, 'a) trans] \<Rightarrow> bool" where
  "closed_delta st al tr \<equiv> \<forall>q\<in>st. \<forall>a\<in>al. tr (q, a) \<in> st"

lemma closed_delta_simp:
  assumes "closed_delta st al tr"
  assumes "q \<in> st"
  assumes "a \<in> al"
  shows "tr (q, a) \<in> st"
  using assms unfolding closed_delta_def by simp

abbreviation st_well_defined :: "('q, 'a, 'e) state_machine_scheme \<Rightarrow> bool" where
  "st_well_defined m \<equiv> initial_in_states (states m) (initial m)
                      \<and> closed_delta (states m) (UNIV::'a set) (delta m)"

lemmas st_well_defined_simps = initial_in_states_def closed_delta_def


definition reachable :: "('q, 'a, 'e) state_machine_scheme \<Rightarrow> 'q \<Rightarrow> bool" where
  "reachable m q \<equiv> (\<exists>w. q = delta_hat m (initial m, w))"

definition trim :: "('q, 'a, 'e) state_machine_scheme \<Rightarrow> bool" where
  "trim m \<equiv> \<forall>q. reachable m q"

section \<open>Properties\<close>

definition star :: "'a set \<Rightarrow> 'a list set" where
  "star A \<equiv> {w. list_all (\<lambda>a. a \<in> A) w}"

lemma star_Cons: "(a#as) \<in> star A \<Longrightarrow> as \<in> star A"
  by (induct as, simp_all add: star_def)

lemma star_append: "u \<in> star A \<Longrightarrow> v \<in> star A \<Longrightarrow> (u @ v) \<in> star A"
  by (induct u, simp_all add: star_def)

lemma closed_delta_hat:
  fixes tr :: "('q, 'a) trans"
  assumes "closed_delta st al tr"
  shows "closed_delta st (star al) (hat1 tr)"
  unfolding closed_delta_def
proof (intro ballI)
  fix q w
  assume q: "q \<in> st"
  assume w: "w \<in> star al"
  { fix q w
    have "q \<in> st \<Longrightarrow> w \<in> star al \<Longrightarrow> hat1 tr (q, w) \<in> st"
      using assms unfolding closed_delta_def
      by (induct w arbitrary: q, simp_all add: star_def)
  }
  then show "hat1 tr (q, w) \<in> st" using q w by simp
qed


lemma delta_append[simp]:
  "hat1 t (q, u @ v) = hat1 t (hat1 t (q, u), v)"
  by (induct u arbitrary: q, auto)

lemma delta_append_1:
  "hat1 t (q, u @ [a]) = t (hat1 t (q, u), a)"
  by (induct u rule: rev_induct, simp_all)

lemma reachable_delta:
  assumes "reachable m q"
  shows "reachable m (delta m (q, a))"
  by (metis assms delta_append_1 reachable_def)

lemma reachable_delta_hat:
  assumes "reachable m q"
  shows "reachable m (delta_hat m (q, w))"
  by (metis assms delta_append reachable_def)

end
