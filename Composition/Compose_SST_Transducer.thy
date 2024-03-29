(* Title:   Compose_SST_Transducer.thy
   Author:  Akama Hitoshi
*)

theory Compose_SST_Transducer
  imports Main HOL.List HOL.Option "../Core/Update" "../Core/Transducer" "../Core/SST"
begin

section \<open>Composition of SST and Transducer\<close>
subsection \<open>Definition of a strange transducer and its property\<close>

(* Combine two transition function (q \<times> x \<Rightarrow> q and q \<times> b \<Rightarrow> q) into a new trans fun *)
fun delta2f ::
  "('q, 'x) trans => ('q, 'b) trans => ('q, 'x + 'b) trans" where
  "delta2f f g (q, Inl x) = f (q, x)" |
  "delta2f f g (q, Inr a) = g (q, a)"

(* eta2f is a function described in Akama's graduate thesis *)
fun eta2f ::
  "('q, 'b, 'c) Transducer.out => ('q, 'x + 'b, 'q \<times> 'x + 'c) Transducer.out" where
  "eta2f e2 (q, Inl x) = [Inl (q, x)]" |
  "eta2f e2 (q, Inr a) = map Inr (e2 (q, a))"

definition \<Delta> :: "('q, 'b) trans
              \<Rightarrow> ('q, 'x) trans \<times> ('z, 'x, 'b) update' \<Rightarrow> ('q, 'z) trans"
  where "\<Delta> t = (\<lambda>(f, \<theta>). (\<lambda>(q, a). hat1 (delta2f f t) (q, \<theta> a)))"

definition H :: "('q, 'b) trans \<Rightarrow> ('q, 'b, 'c) out
              \<Rightarrow> ('q, 'x) trans \<times> ('a, 'x, 'b) update' \<Rightarrow> ('q \<times> 'a, 'q \<times> 'x, 'c) update'"
  where "H tr to = (\<lambda>(f, \<theta>). (\<lambda>(q, a). Transducer.hat2 (delta2f f tr) (eta2f to) (q, \<theta> a)))"


proposition \<Delta>_assoc_string:
  "hat1 (delta2f (\<lambda>(q, a). hat1 (delta2f f tr) (q, theta a)) tr) (q, u) =
   hat1 (delta2f f tr) (q, hat_hom theta u)"
  by (induct u arbitrary: q rule: xa_induct, simp_all)

lemma \<Delta>_assoc: "\<Delta> t (f, \<phi> \<bullet> \<psi>) = \<Delta> t (\<Delta> t (f, \<phi>), \<psi>)"
  by (auto simp add: \<Delta>_def compU_apply \<Delta>_assoc_string)

proposition H_assoc_string:
  "hat_hom (\<lambda>(q2, x1). Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (q2, theta x1))
     (Transducer.hat2 (delta2f (\<lambda>(q2, x1). hat1 (delta2f f t_trans) (q2, theta x1)) t_trans) (eta2f t_out) (q, u)) =
   Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (q, hat_hom theta u)"
  by (induct u arbitrary: q rule: xa_induct, simp_all add: Transducer.eta_append)

lemma H_assoc: "H tr to (f, \<phi> \<bullet> \<psi>) = H tr to (f, \<phi>) \<bullet> H tr to (\<Delta> tr (f, \<phi>), \<psi>)"
  by (auto simp add: \<Delta>_def H_def compU_apply H_assoc_string)


subsection \<open>Construction\<close>

definition compose_\<delta> :: "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'a) trans" where
  "compose_\<delta> sst td = (\<lambda>((q1, f), a). (delta sst (q1, a),
                                         \<Delta> (delta td) (f, eta sst (q1, a))))"

definition compose_\<eta> :: "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'a, 'c) updator" where
  "compose_\<eta> sst td = (\<lambda>((q1, f), a). H (delta td) (Transducer.eta td) (f, eta sst (q1, a)))"

definition compose_final :: "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2) \<Rightarrow> ('q2 \<times> 'x1 + 'c) list option)" where
  "compose_final sst td = (\<lambda>(q1, f).
     case final sst q1 of
       Some u \<Rightarrow>
         if Transducer.final td (\<Delta> (delta td) (f, \<lambda>x. u) (initial td, ()))
         then Some (H (delta td) (Transducer.eta td) (f, \<lambda>x. u)
                      (initial td, ()))
         else None |
       None \<Rightarrow> None)"

definition compose_SST_Transducer ::
  "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'a, 'c) SST" where
  "compose_SST_Transducer sst td = \<lparr>
    initial = (initial sst, \<lambda>(q2, x1). q2),
    delta   = compose_\<delta> sst td,
    eta     = compose_\<eta> sst td,
    final   = compose_final sst td
   \<rparr>"

lemma compose_\<delta>_hat: "hat1 (compose_\<delta> sst td) ((q, f), w) =
        (delta_hat sst (q, w),
         \<Delta> (delta td) (f, eta_hat sst (q, w)))"
proof (induct w arbitrary: q f)
  case Nil then show ?case by (simp add: idU_def \<Delta>_def)
next
  case (Cons a u) then show ?case by (simp add: compose_\<delta>_def \<Delta>_assoc)
qed

lemma compose_\<eta>_hat:
  "hat2 (compose_\<delta> sst td) (compose_\<eta> sst td) ((q, f), w) =
   H (delta td) (Transducer.eta td) (f, eta_hat sst (q, w))"
proof (induct w arbitrary: q f)
  case Nil then show ?case by (simp add: idU_def H_def)
next
  case (Cons a u) then show ?case by (simp add: compose_\<delta>_def compose_\<eta>_def H_assoc)
qed


subsection \<open>Property of valuation\<close>


lemma valuate_delta_hat_string: "hat1 (delta2f (\<lambda>(q, x). q) tr) (q, w) = hat1 tr (q, valuate w)"
  by (induct w arbitrary: q rule: xa_induct, simp_all add: empty_def)

lemma valuate_delta_hat: "hat1 tr (q, valuate (u x)) = \<Delta> tr (\<lambda>(q, x). q, u) (q, x)"
  by (simp add: comp_def \<Delta>_def valuate_delta_hat_string)

lemma valuate_eta_hat_string:
  "valuate (Transducer.hat2 (delta2f (\<lambda>(q2, x). q2) tr) (eta2f td) (q, w))
 = Transducer.hat2 tr td (q, valuate w)"
  by (induct w arbitrary: q rule: xa_induct, simp_all)

lemma valuate_eta_hat: "Transducer.hat2 tr td (q, valuate (u x)) = valuate (H tr td (\<lambda>(q, x). q, u) (q, x))"
  by (simp add: H_def valuate_eta_hat_string)


subsection \<open>Main results\<close>

theorem can_compose_SST_Transducer:
  fixes sst :: "('q1, 'x, 'a, 'b) SST"
  fixes td  :: "('q2, 'b, 'c) transducer"
  shows "SST.run (compose_SST_Transducer sst td) w
       = Option.bind (SST.run sst w) (Transducer.run td)"
proof (cases "SST.final sst (delta_hat sst (initial sst, w))")
  case None then show ?thesis
    by (simp add: compose_SST_Transducer_def SST.run_def Transducer.run_def compose_final_def compose_\<delta>_hat)
next
  case (Some output_final1)
  let ?output_of_1st_sst =
    "valuate ((SST.eta_hat sst (initial sst, w) \<bullet> (\<lambda>x. output_final1)) ())"
  show ?thesis
  proof (cases "transducer.final td (delta_hat td (initial td, ?output_of_1st_sst))")
    case False then show ?thesis
      by (simp add: SST.run_def Transducer.run_def Some
            compose_SST_Transducer_def compose_\<delta>_hat compose_final_def valuate_delta_hat \<Delta>_assoc)
  next
    case True then show ?thesis
      by (simp add: SST.run_def compose_SST_Transducer_def compose_final_def
                       Transducer.run_def compose_\<delta>_hat compose_\<eta>_hat Some
                       \<Delta>_assoc valuate_delta_hat
                       compU_ignore
                       valuate_eta_hat
                       H_assoc)
  qed
qed

end
