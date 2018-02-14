theory Compose_SST_Transducer
  imports Main Update Transducer SST
begin


(* split the final function into the output function and accept function *)
record ('q, 'x, 'a, 'b) SST2 = 
  initial :: "'q"
  delta :: "('q, 'a) trans_f"
  eta :: "('q, 'x, 'a, 'b) update_f"
  final :: "'q \<Rightarrow> ('x + 'b) list"
  accept :: "'q \<Rightarrow> bool"

definition split_SST :: "('q, 'x, 'a, 'b) SST \<Rightarrow> ('q, 'x, 'a, 'b) SST2" where
  "split_SST sst = \<lparr>
    initial = SST.initial sst,
    delta = SST.delta sst,
    eta = SST.eta sst,
    final = (\<lambda>q. case SST.final sst q of Some(template) \<Rightarrow> template | None \<Rightarrow> Nil),
    accept = (\<lambda>q. case SST.final sst q of Some(_) \<Rightarrow> True | None \<Rightarrow> False)
  \<rparr>"

(* BUG: we don't care accept or not, now *)
definition run_SST2 :: "('q, 'x, 'a, 'b) SST2 \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "run_SST2 sst w = (let q = SST.hat1 (delta sst) (initial sst, w)
                     in let \<xi> = SST.hat2 (delta sst) (eta sst) (initial sst, w)
                     in if accept sst q
                     then Some (valuate (((\<lambda>x. [] :: ('x + 'b) list) \<bullet> \<xi> \<bullet> final sst) q))
                     else None)"

term "SOME x. True"

definition run_total_SST2 :: "('q, 'x, 'a, 'b) SST2 \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "run_total_SST2 sst w = (let q = SST.hat1 (delta sst) (initial sst, w)
                     in let \<xi> = SST.hat2 (delta sst) (eta sst) (initial sst, w)
                     in valuate (((\<lambda>x. ([] :: ('x + 'b) list)) \<bullet> \<xi> \<bullet> (\<lambda>x. final sst q)) (SOME x :: 'x. True)))"


(* This file includes a proof of SST-Transducer composition (in progress) 
   using NEW NOTATION (such as \<Delta>, H, ...) *)

definition \<Delta> :: "('q, 'b) trans
              \<Rightarrow> ('q, 'x) trans \<times> ('z, 'x, 'b) update' \<Rightarrow> ('q, 'z) trans"
  where "\<Delta> t = (\<lambda>(f, \<theta>). (\<lambda>(q, a). hat1 (delta2f f t) (q, \<theta> a)))"
    
definition H :: "('q, 'b) trans \<Rightarrow> ('q, 'b, 'c) out 
              \<Rightarrow> ('q, 'x) trans \<times> ('a, 'x, 'b) update' \<Rightarrow> ('q \<times> 'a, 'q \<times> 'x, 'c) update'"
  where "H tr to = (\<lambda>(f, \<theta>). (\<lambda>(q, a). Transducer.hat2 (delta2f f tr) (eta2f to) (q, \<theta> a)))"


(* those lemmata are unfinished, but can construct from 
  lemma delta2f_apply_hat and eta2f_apply_hat in SST.thy *)
lemma \<Delta>_assoc: "\<Delta> t (f, \<phi> \<bullet> \<psi>) = \<Delta> t (\<Delta> t (f, \<phi>), \<psi>)"
  sorry

lemma H_assoc: "H tr to (f, \<phi> \<bullet> \<psi>) = H tr to (f, \<phi>) \<bullet> H tr to (\<Delta> tr (f, \<phi>), \<psi>)"
  sorry


definition compose_\<delta> :: "('q1, 'x1, 'a, 'b) SST2 \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'a) trans" where
  "compose_\<delta> sst td = (\<lambda>((q1, f), a). (delta sst (q1, a),
                                         \<Delta> (Transducer.delta td) (f, eta sst (q1, a))))"
  
definition compose_\<eta> :: "('q1, 'x1, 'a, 'b) SST2 \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'a, 'c) update_f" where
  "compose_\<eta> sst td = (\<lambda>((q1, f), a). H (Transducer.delta td) (Transducer.eta td) (f, eta sst (q1, a)))"

definition compose_final :: "('q1, 'x1, 'a, 'b) SST2 \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2) \<Rightarrow> ('q2 \<times> 'x1 + 'c) list)" where
  "compose_final sst td = (\<lambda>(q1, f). H (Transducer.delta td) (Transducer.eta td) (f, \<lambda>x. final sst q1) (Transducer.initial td, SOME x :: 'x1. True))"

definition compose_accept :: "('q1, 'x1, 'a, 'b) SST2 \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
                              ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2) \<Rightarrow> bool)" where
  "compose_accept sst td = (\<lambda>(q1, f). accept sst q1 \<and>
                            Transducer.final td (\<Delta> (Transducer.delta td) (f, final sst) (Transducer.initial td, q1)))"


definition compose_SST_Transducer ::
  "('q1, 'x1, 'a, 'b) SST2 \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'a, 'c) SST2" where
  "compose_SST_Transducer sst td = \<lparr>
    initial = (initial sst, \<lambda>(q2, x1) \<Rightarrow> q2),
    delta = compose_\<delta> sst td,
    eta = compose_\<eta> sst td,
    final = compose_final sst td,
    accept = compose_accept sst td
   \<rparr>"

lemma compose_\<delta>_hat: "hat1 (compose_\<delta> sst td) ((q, f), w) =
        (hat1 (delta sst) (q, w),
         \<Delta> (Transducer.delta td) (f, SST.hat2 (delta sst) (eta sst) (q, w)))"
proof (induction w arbitrary: q f)
  case Nil
  show ?case by (simp add: idU_def \<Delta>_def)
next
  case (Cons a u)
(*  show ?case 
    thm Cons
    thm Cons[simplified compose_delta_def case_prod_beta] 
    apply simp
    apply (simp add: Cons.IH \<Delta>_assoc)
*)
  have "compose_\<delta> sst td ((q, f), a)
      = (delta sst (q, a), \<Delta> (Transducer.delta td) (f, eta sst (q, a)))"
    by (simp add: compose_\<delta>_def)
  thus ?case
    by (simp add: Cons.IH \<Delta>_assoc)
qed      

lemma compose_\<eta>_hat:
  "hat2 (compose_\<delta> sst td) (compose_\<eta> sst td) ((q, f), w) =
   H (Transducer.delta td) (Transducer.eta td) (f, hat2 (delta sst) (eta sst) (q, w))"
proof (induction w arbitrary: q f)
  case Nil
  show ?case by (simp add: idU_def H_def)
next
  case (Cons a u)
  have "compose_\<delta> sst td ((q, f), a) 
     = (delta sst (q, a), \<Delta> (Transducer.delta td) (f, eta sst (q, a)))"
    by (simp add: compose_\<delta>_def)
  moreover have "compose_\<eta> sst td ((q, f), a) = H (Transducer.delta td) (Transducer.eta td) (f, eta sst (q, a))"
    by (simp add: compose_\<eta>_def)
  ultimately show ?case
    by (simp add: Cons.IH H_assoc)
qed


lemma initial_delta: "\<Delta> tr (\<lambda>(q, x). q, \<lambda>x. []) = (\<lambda>(q, x). q)"
  by (simp add: \<Delta>_def)

lemma initial_eta: "H tr to (\<lambda>(q, x). q, \<lambda>x. []) = (\<lambda>(q, x). [])"
  by (simp add: H_def)

lemma valuate_distrib: "valuate (as @ bs) == valuate as @ valuate bs"
proof (induction as)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case by (cases a, simp+)
qed

lemma valuate_map: "valuate (map Inr as) = as"
  by (induction as, auto)

lemma valuate_eta_hat_0: "valuate (Transducer.hat2 (delta2f (\<lambda>(q, x). q) tr) (eta2f td) (q, w)) = Transducer.hat2 tr td (q, valuate w)"
proof (induction w arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case proof (cases a)
    case (Inl a)
    then show ?thesis by (simp add: Cons.IH)
  next
    case (Inr b)
    then show ?thesis by (simp add: Cons.IH valuate_distrib valuate_map)
  qed
qed


lemma valuate_eta_hat: "valuate (H tr td (\<lambda>(q, x). q, u) (q2_0, x)) = Transducer.hat2 tr td (q2_0, valuate (u x))"
  by (simp add: H_def valuate_eta_hat_0)

lemma valuate_eta_hat_2:
  assumes "u (q2_0, x) = H tr td (\<lambda>(q, x). q, u') (q2_0, x)"
  shows "valuate (u (q2_0, x)) = Transducer.hat2 tr td (q2_0, valuate (u' x))"
  using assms by (simp add: valuate_eta_hat)



(* TODO: this is total version of composition *)
theorem can_compose_SST_Transducer_total: 
  "run_total_SST2 (compose_SST_Transducer sst td) w
 = Transducer.run_total td (run_total_SST2 sst w)"
proof -
  let ?tr = "Transducer.delta td"
  let ?to = "Transducer.eta td"
  let ?f0 = "\<lambda>(q, x). q"
  let ?e0 = "\<lambda>x. []"
  let ?q' = "SST.hat1 (SST2.delta sst) (SST2.initial sst, w)"
  let ?xi = "SST.hat2 (SST2.delta sst) (SST2.eta sst) (SST2.initial sst, w)"
  have H_inner: "H ?tr ?to (?f0, ?e0 \<bullet> ?xi \<bullet> (\<lambda>x. SST2.final sst ?q'))
      = H ?tr ?to (?f0, ?e0) \<bullet> H ?tr ?to (?f0, ?xi) \<bullet> H ?tr ?to (\<Delta> ?tr (?f0, ?xi), (\<lambda>x. SST2.final sst ?q'))"
    by (simp add: H_assoc initial_delta)
  
  show ?thesis
    apply (simp add: compose_SST_Transducer_def run_total_SST2_def run_total_def compose_final_def compose_\<delta>_hat compose_\<eta>_hat)
    apply (rule valuate_eta_hat_2[where u' = "(\<lambda>x. []) \<bullet> SST.hat2 (SST2.delta sst) (SST2.eta sst) (SST2.initial sst, w) \<bullet> (\<lambda>x. SST2.final sst (SST.hat1 (SST2.delta sst) (SST2.initial sst, w)))"])
    apply (simp add: H_inner initial_eta)
    thm valuate_eta_hat_2[where u' = "(\<lambda>x. []) \<bullet> SST.hat2 (SST2.delta sst) (SST2.eta sst) (SST2.initial sst, w) \<bullet> (\<lambda>x. SST2.final sst (SST.hat1 (SST2.delta sst) (SST2.initial sst, w)))"]
    
(*
    ((\<lambda>x. []) \<bullet> SST.hat2 (SST2.delta sst) (SST2.eta sst) (SST2.initial sst, w) \<bullet> (\<lambda>x. SST2.final sst (SST.hat1 (SST2.delta sst) (SST2.initial sst, w)
*)