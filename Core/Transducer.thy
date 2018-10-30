theory Transducer
  imports Main State_Machine
begin

type_synonym ('q, 'a, 'b) "out" =
  "'q \<times> 'a \<Rightarrow> 'b list"


record ('q, 'a, 'b) transducer = "('q, 'a) state_machine" +
  eta :: "('q, 'a, 'b) out"
  final :: "'q \<Rightarrow> bool"


fun hat2 :: "('q, 'a) trans \<Rightarrow> ('q, 'a, 'b) out \<Rightarrow> ('q, 'a list, 'b) out" where
  "hat2 t outf (q, [])   = []" |
  "hat2 t outf (q, a#as) = outf (q, a) @ hat2 t outf (t (q, a), as)"

(* \<eta>^(q, w) *)
abbreviation eta_hat :: "('q, 'a, 'b, 'e) transducer_scheme \<Rightarrow> ('q, 'a list, 'b) out" where
  "eta_hat sst \<equiv> hat2 (delta sst) (eta sst)"


definition run :: "('q, 'a, 'b, 'e) transducer_scheme \<Rightarrow> 'a list \<Rightarrow> ('b list) option" where
  "run T as = (if final T (hat1 (delta T) (initial T, as))
               then Some (hat2 (delta T) (eta T) (initial T, as))
               else None)"


definition compose_delta ::
  "('q1, 'a, 'b) transducer => ('q2, 'b, 'c) transducer => ('q1 \<times> 'q2, 'a) trans" where
  "compose_delta T1 T2 = (\<lambda>((q1, q2), a). (delta T1 (q1, a), hat1 (delta T2) (q2, eta T1 (q1, a))))"

definition compose_eta ::
  "('q1, 'a, 'b) transducer => ('q2, 'b, 'c) transducer => ('q1 \<times> 'q2, 'a, 'c) out" where
  "compose_eta T1 T2 = (\<lambda>((q1, q2), a). hat2 (delta T2) (eta T2) (q2, (eta T1 (q1, a))))"

definition compose :: "('q1, 'a, 'b) transducer => ('q2, 'b, 'c) transducer =>
                ('q1 \<times> 'q2, 'a, 'c) transducer" where
  "compose T1 T2 = (|
    initial = (initial T1, initial T2),
    delta = compose_delta T1 T2,
    eta = compose_eta T1 T2,
    final = \<lambda>(q1, q2). final T1 q1 \<and> final T2 q2
 |)"

lemma compose_delta_hat: "hat1 (compose_delta T1 T2) ((q1, q2), w) =
      (hat1 (delta T1) (q1, w), hat1 (delta T2) (q2, hat2 (delta T1) (eta T1) (q1, w)))"
  by (induction w arbitrary: q1 q2, auto simp add: compose_delta_def)

lemma eta_append: "hat2 t f (q, as @ bs) = hat2 t f (q, as) @ hat2 t f (hat1 t (q, as), bs)"
  by (induction as arbitrary: q, auto)

lemma compose_eta_hat: "hat2 (compose_delta T1 T2) (compose_eta T1 T2) ((q1, q2), w) =
       hat2 (delta T2) (eta T2) (q2, hat2 (delta T1) (eta T1) (q1, w))"
  by (induction w arbitrary: q1 q2,
      auto simp add: compose_delta_def compose_eta_def eta_append)

theorem compose_Transducer_Transducer:
  "run (compose T1 T2) w = (case run T1 w of Some u => run T2 u | None => None)"
  by (auto simp add: run_def compose_def compose_delta_hat compose_eta_hat)


end
