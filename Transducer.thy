theory Transducer
  imports Main
begin

type_synonym ('q, 'a) "trans" =
  "'q \<times> 'a \<Rightarrow> 'q"

type_synonym ('q, 'a, 'b) "out" =
  "'q \<times> 'a \<Rightarrow> 'b list"


record ('q, 'a, 'b) transducer =
  states :: "'q set"
  initial :: "'q"
  delta :: "('q, 'a) trans"
  eta :: "('q, 'a, 'b) out"
  final :: "'q \<Rightarrow> bool"


fun hat1 :: "('q, 'a) trans \<Rightarrow> ('q, 'a list) trans" where
  "hat1 t (q, [])   = q" |
  "hat1 t (q, a#as) = hat1 t (t (q, a), as)"

fun hat2 :: "('q, 'a) trans \<Rightarrow> ('q, 'a, 'b) out \<Rightarrow> ('q, 'a list, 'b) out" where
  "hat2 t outf (q, [])   = []" |
  "hat2 t outf (q, a#as) = outf (q, a) @ hat2 t outf (t (q, a), as)"

(* \<delta>\<^sup>^(q, w) *)
abbreviation delta_hat :: "('q, 'a, 'b) transducer \<Rightarrow> ('q, 'a list) trans" where
  "delta_hat sst \<equiv> hat1 (delta sst)"

(* \<eta>^(q, w) *)
abbreviation eta_hat :: "('q, 'a, 'b) transducer \<Rightarrow> ('q, 'a list, 'b) out" where
  "eta_hat sst \<equiv> hat2 (delta sst) (eta sst)"


definition run :: "('q, 'a, 'b) transducer \<Rightarrow> 'a list \<Rightarrow> ('b list) option" where
  "run T as = (if final T (hat1 (delta T) (initial T, as))
               then Some (hat2 (delta T) (eta T) (initial T, as))
               else None)"

definition run_total :: "('q, 'a, 'b) transducer \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "run_total T as = (let q' = hat1 (delta T) (initial T, as) in
                     let bs = hat2 (delta T) (eta T) (initial T, as)
                     in bs)"

definition td_well_defined where
  "td_well_defined T \<equiv> (initial T \<in> states T) \<and> (\<forall>q\<in>states T. \<forall>a. delta T (q, a) \<in> states T)"

lemma td_closed_delta_hat:
  assumes "td_well_defined T"
  assumes "q \<in> states T"
  shows "delta_hat T (q, w) \<in> states T"
using assms by (induct w arbitrary: q, simp_all add: td_well_defined_def)


definition compose_delta ::
  "('q1, 'a, 'b) transducer => ('q2, 'b, 'c) transducer => ('q1 \<times> 'q2, 'a) trans" where
  "compose_delta T1 T2 = (\<lambda>((q1, q2), a). (delta T1 (q1, a), hat1 (delta T2) (q2, eta T1 (q1, a))))"

definition compose_eta ::
  "('q1, 'a, 'b) transducer => ('q2, 'b, 'c) transducer => ('q1 \<times> 'q2, 'a, 'c) out" where
  "compose_eta T1 T2 = (\<lambda>((q1, q2), a). hat2 (delta T2) (eta T2) (q2, (eta T1 (q1, a))))"



definition compose :: "('q1, 'a, 'b) transducer => ('q2, 'b, 'c) transducer =>
                ('q1 \<times> 'q2, 'a, 'c) transducer" where
  "compose T1 T2 = (|
    states = states T1 \<times> states T2,
    initial = (initial T1, initial T2),
    delta = compose_delta T1 T2,
    eta = compose_eta T1 T2,
    final = \<lambda>(q1, q2). final T1 q1 \<and> final T2 q2
 |)"


lemma delta_append: "hat1 t (q, as @ bs) = hat1 t (hat1 t (q, as), bs)"
by (induction as arbitrary: q, auto)


lemma compose_delta_hat: "hat1 (compose_delta T1 T2) ((q1, q2), w) =
      (hat1 (delta T1) (q1, w), hat1 (delta T2) (q2, hat2 (delta T1) (eta T1) (q1, w)))"
by (induction w arbitrary: q1 q2, auto simp add: compose_delta_def delta_append)


lemma eta_append: "hat2 t f (q, as @ bs) = hat2 t f (q, as) @ hat2 t f (hat1 t (q, as), bs)"
by (induction as arbitrary: q, auto)

lemma compose_eta_hat: "hat2 (compose_delta T1 T2) (compose_eta T1 T2) ((q1, q2), w) =
       hat2 (delta T2) (eta T2) (q2, hat2 (delta T1) (eta T1) (q1, w))"
by (induction w arbitrary: q1 q2,
    auto simp add: compose_delta_def compose_eta_def eta_append)

theorem 
  assumes "td_well_defined T1"
  assumes "td_well_defined T2"
  shows "td_well_defined (compose T1 T2)"
proof (auto simp add: td_well_defined_def)
  show "initial (compose T1 T2) \<in> states (compose T1 T2)"
    using assms unfolding td_well_defined_def compose_def
    by auto
next
  fix q1 q2 a
  assume "(q1, q2) \<in> states (compose T1 T2)"
  then have q: "q1 \<in> states T1 \<and> q2 \<in> states T2" 
    by (simp add: compose_def)
  show "delta (compose T1 T2) ((q1, q2), a) \<in> states (compose T1 T2)"
    unfolding compose_def compose_delta_def td_well_defined_def
  proof (auto)
    show "delta T1 (q1, a) \<in> states T1"
      using assms q unfolding td_well_defined_def by simp
  next
    show "delta_hat T2 (q2, eta T1 (q1, a)) \<in> states T2"
      apply (rule td_closed_delta_hat)
      using assms q by auto
  qed
qed

theorem "run (compose T1 T2) w = (case run T1 w of Some u => run T2 u | None => None)"
by (auto simp add: run_def compose_def compose_delta_hat compose_eta_hat)


lemma "hat1 t (q, (as @ bs)) = hat1 t (hat1 t (q, as), bs)"
proof (induction as arbitrary: q)
  case Nil
  show ?case
    apply (simp only: List.append.left_neutral)
    apply (simp only: hat1.simps(1))
    done
next
  case (Cons a as)
  show ?case
    apply simp
    apply (rule Cons.IH)
    done
qed

end
