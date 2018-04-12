(* Title:   Compose_SST_SST.thy
   Author:  Akama Hitoshi
*)

section \<open>Composition of SST and SST\<close>

theory Compose_SST_SST
  imports Main List Option Update Transducer SST Monoid_SST
begin

subsection \<open>Definition of a strange transducer and its property\<close>

(* Combine two transition function (q \<times> x \<Rightarrow> q and q \<times> b \<Rightarrow> q) into a new trans fun *)
fun delta2f ::
  "('q, 'x) trans => ('q, 'b) trans => ('q, 'x + 'b) trans" where
  "delta2f f g (q, Inl x) = f (q, x)" |
  "delta2f f g (q, Inr a) = g (q, a)"

(* eta2f is a function described in Akama's graduate thesis *)
fun eta2f ::
  "('q2, 'y, 'b, 'c) SST.updator => ('q2, 'x + 'b, 'q2 \<times> 'x + ('y, 'c) update) Transducer.out" where
  "eta2f e2 (q2, Inl x) = [Inl (q2, x)]" |
  "eta2f e2 (q2, Inr b) = [Inr (e2 (q2, b))]"

definition \<Delta> :: "('q, 'b) trans
              \<Rightarrow> ('q, 'x) trans \<times> ('z, 'x, 'b) update' \<Rightarrow> ('q, 'z) trans"
  where "\<Delta> t = (\<lambda>(f, \<theta>). (\<lambda>(q, a). hat1 (delta2f f t) (q, \<theta> a)))"

definition H :: "('q2, 'b) trans \<Rightarrow> ('q2, 'x2, 'b, 'c) updator
              \<Rightarrow> ('q2, 'x1) trans \<times> ('x1, 'b) update => ('q2 \<times> 'x1, ('x2, 'c) update) update"
  where "H tr to = (\<lambda>(f, \<theta>). (\<lambda>(q, a). Transducer.hat2 (delta2f f tr) (eta2f to) (q, \<theta> a)))"


proposition \<Delta>_assoc_string:
  "hat1 (delta2f (\<lambda>(q, a). hat1 (delta2f f tr) (q, theta a)) tr) (q, u) =
   hat1 (delta2f f tr) (q, hat_hom theta u)"
  by (induction u arbitrary: q rule: xa_induct, simp_all add: delta_append)

lemma \<Delta>_assoc: "\<Delta> t (f, \<phi> \<bullet> \<psi>) = \<Delta> t (\<Delta> t (f, \<phi>), \<psi>)"
  by (auto simp add: \<Delta>_def comp_def \<Delta>_assoc_string)

proposition H_assoc_string:
  "hat_hom (\<lambda>(q2, x1). Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (q2, theta x1))
     (Transducer.hat2 (delta2f (\<lambda>(q2, x1). hat1 (delta2f f t_trans) (q2, theta x1)) t_trans) (eta2f t_out) (q, u)) =
   Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (q, hat_hom theta u)"
  by (induction u arbitrary: q rule: xa_induct,
       simp_all add: Transducer.eta_append hat_hom_right_ignore)

lemma H_assoc: "H tr to (f, \<phi> \<bullet> \<psi>) = H tr to (f, \<phi>) \<bullet> H tr to (\<Delta> tr (f, \<phi>), \<psi>)"
  by (auto simp add: \<Delta>_def H_def comp_def H_assoc_string)

subsection \<open>Construction\<close>

definition compose_\<delta> :: "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'x2, 'b, 'c) SST \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'a) trans" where
  "compose_\<delta> sst1 sst2 =
     (\<lambda>((q1, f), a). (SST.delta sst1 (q1, a), \<Delta> (SST.delta sst2) (f, SST.eta sst1 (q1, a))))"

definition compose_\<eta> :: "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'x2, 'b, 'c) SST \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'a, ('x2, 'c) update) updator" where
  "compose_\<eta> sst1 sst2 = (\<lambda>((q1, f), a). H (SST.delta sst2) (SST.eta sst2) (f, SST.eta sst1 (q1, a)))"

definition compose_final_update ::
  "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'x2, 'b, 'c) SST \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2) \<Rightarrow> ('q2 \<times> 'x1 + ('x2, 'c) update) list option)" where
  "compose_final_update sst1 sst2 = (\<lambda>(q1, f).
     case SST.final sst1 q1 of
       Some u \<Rightarrow> Some (H (SST.delta sst2) (SST.eta sst2) (f, \<lambda>x. u)
                        (SST.initial sst2, SOME x :: 'x1. True)) |
       None \<Rightarrow> None)"

definition compose_final_string ::
  "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'x2, 'b, 'c) SST \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2) \<Rightarrow> ('x2 + 'c) list option)" where
  "compose_final_string sst1 sst2 = (\<lambda>(q1, f).
     case SST.final sst1 q1 of
       Some u \<Rightarrow> SST.final sst2 (\<Delta> (SST.delta sst2) (f, \<lambda>x. u) (SST.initial sst2, SOME x :: 'x1. True)) |
       None \<Rightarrow> None)"

definition compose_SST_SST ::
  "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'x2, 'b, 'c) SST \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'x2, 'a, 'c) MSST" where
  "compose_SST_SST sst1 sst2 = \<lparr>
    initial = (SST.initial sst1, \<Delta> (SST.delta sst2) (\<lambda>(q2, x1). q2, emptyU)),
    delta   = compose_\<delta> sst1 sst2,
    eta     = compose_\<eta> sst1 sst2,
    final_update = compose_final_update sst1 sst2,
    final_string = compose_final_string sst1 sst2
   \<rparr>"

lemma compose_\<delta>_hat: "hat1 (compose_\<delta> sst1 sst2) ((q, f), w) =
        (SST.delta_hat sst1 (q, w),
         \<Delta> (SST.delta sst2) (f, SST.eta_hat sst1 (q, w)))"
proof (induction w arbitrary: q f)
  case Nil then show ?case by (simp add: idU_def \<Delta>_def)
next
  case (Cons a u) then show ?case by (simp add: compose_\<delta>_def \<Delta>_assoc)
qed

lemma compose_\<eta>_hat:
  "hat2 (compose_\<delta> sst1 sst2) (compose_\<eta> sst1 sst2) ((q, f), w) =
   H (SST.delta sst2) (SST.eta sst2) (f, SST.eta_hat sst1 (q, w))"
proof (induction w arbitrary: q f)
  case Nil then show ?case by (simp add: idU_def H_def)
next
  case (Cons a u) then show ?case by (simp add: compose_\<delta>_def compose_\<eta>_def H_assoc)
qed


subsection \<open>Property of valuation and empty update\<close>

lemma initial_eta: "H tr to (\<lambda>(q, x). q, emptyU) = emptyU"
  by (auto simp add: H_def emptyU_def)

lemma valuate_delta_hat_string: "hat1 (delta2f (\<lambda>(q, x). q) tr) (q, w) = hat1 tr (q, valuate w)"
  by (induction w arbitrary: q rule: xa_induct, simp_all add: empty_def)

lemma valuate_delta_hat: "hat1 tr (q, valuate (u x)) = \<Delta> tr (\<lambda>(q, x). q, u) (q, x)"
  by (simp add: comp_def \<Delta>_def valuate_delta_hat_string)

lemma valuate_eta_hat_string:
  "concatU (valuate (Transducer.hat2 (delta2f (\<lambda>(q2, x). q2) tr) (eta2f td) (q, w)))
 = SST.hat2 tr td (q, valuate w)"
  by (induction w arbitrary: q rule: xa_induct, simp_all)

lemma valuate_eta_hat: "SST.hat2 tr td (q, valuate (u x)) = concatU (valuate (H tr td (\<lambda>(q, x). q, u) (q, x)))"
  by (simp add: H_def valuate_eta_hat_string)


subsection \<open>Main result\<close>

theorem can_compose_SST_SST:
  fixes sst1 :: "('q1, 'x1, 'a, 'b) SST"
  fixes sst2 :: "('q2, 'x2, 'b, 'c) SST"
  shows "Monoid_SST.run (compose_SST_SST sst1 sst2) w
       = Option.bind (SST.run sst1 w) (SST.run sst2)"
proof (cases "SST.final sst1 (SST.delta_hat sst1 (SST.initial sst1, w))")
  case None then show ?thesis
    by (simp add: compose_SST_SST_def SST.run_def Monoid_SST.run_def compose_final_update_def compose_\<delta>_hat)
next
  case Some_1: (Some output_final1)
  let ?output_of_1st_sst =
    "valuate ((emptyU \<bullet> SST.eta_hat sst1 (SST.initial sst1, w) \<bullet> (\<lambda>x. output_final1)) (SOME x :: 'x1. True))"
  show ?thesis
  proof (cases "SST.final sst2 (SST.delta_hat sst2 (SST.initial sst2, ?output_of_1st_sst))")
    case None then show ?thesis
      by (simp add: SST.run_def Monoid_SST.run_def Transducer.run_def Some_1
          compose_SST_SST_def compose_\<delta>_hat compose_final_update_def compose_final_string_def valuate_delta_hat \<Delta>_assoc)
  next
    case Some_2: (Some output_final2) then show ?thesis
      by (simp add: SST.run_def Monoid_SST.run_def compose_SST_SST_def
               compose_final_update_def compose_final_string_def
               Transducer.run_def compose_\<delta>_hat compose_\<eta>_hat Some_2
                       \<Delta>_assoc valuate_delta_hat
                       comp_ignore
                       valuate_eta_hat
                       H_assoc
                       initial_eta
                       Some_1)
  qed
qed

end
