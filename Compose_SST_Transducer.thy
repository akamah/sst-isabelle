theory Compose_SST_Transducer
  imports Main Update Transducer SST
begin

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


definition compose_\<delta> :: "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'a) trans" where
  "compose_\<delta> sst td = (\<lambda>((q1, f), a). (SST.delta sst (q1, a),
                                         \<Delta> (Transducer.delta td) (f, SST.eta sst (q1, a))))"
  
definition compose_\<eta> :: "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'a, 'c) update_f" where
  "compose_\<eta> sst td = (\<lambda>((q1, f), a). H (Transducer.delta td) (Transducer.eta td) (f, SST.eta sst (q1, a)))"

definition compose_F :: "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2) \<Rightarrow> ('q2 \<times> 'x1 + 'c) list option)" where
  "compose_F sst td = (\<lambda>(q1, f).
     case SST.final sst q1 of
       Some(out) \<Rightarrow> (
         let q2 = \<Delta> (Transducer.delta td)                     (f, \<lambda>_. out) (Transducer.initial td, q1)
         in let o' = H (Transducer.delta td) (Transducer.eta td) (f, \<lambda>_. out) (Transducer.initial td, q1)
         in case Transducer.final td q2 of
           True \<Rightarrow> Some o' |
           False \<Rightarrow> None) |
       None \<Rightarrow> None)"

definition compose_SST_Transducer ::
  "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'a, 'c) SST" where
  "compose_SST_Transducer sst td = \<lparr>
    initial = (SST.initial sst, \<lambda>(q2, x1) \<Rightarrow> q2),
    delta = compose_\<delta> sst td,
    eta = compose_\<eta> sst td,
    final = compose_F sst td
   \<rparr>"

lemma compose_\<delta>_hat: "hat1 (compose_\<delta> sst td) ((q, f), w) =
        (hat1 (SST.delta sst) (q, w),
         \<Delta> (Transducer.delta td) (f, SST.hat2 (SST.delta sst) (SST.eta sst) (q, w)))"
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
      = (SST.delta sst (q, a), \<Delta> (Transducer.delta td) (f, SST.eta sst (q, a)))"
    by (simp add: compose_\<delta>_def)
  thus ?case
    by (simp add: Cons.IH \<Delta>_assoc)
qed      

lemma compose_\<eta>_hat:
  "hat2 (compose_\<delta> sst td) (compose_\<eta> sst td) ((q, f), w) =
   H (Transducer.delta td) (Transducer.eta td) (f, hat2 (SST.delta sst) (SST.eta sst) (q, w))"
proof (induction w arbitrary: q f)
  case Nil
  show ?case by (simp add: idU_def H_def)
next
  case (Cons a u)
  have "compose_\<delta> sst td ((q, f), a) 
     = (SST.delta sst (q, a), \<Delta> (Transducer.delta td) (f, SST.eta sst (q, a)))"
    by (simp add: compose_\<delta>_def)
  moreover have "compose_\<eta> sst td ((q, f), a) = H (Transducer.delta td) (Transducer.eta td) (f, SST.eta sst (q, a))"
    by (simp add: compose_\<eta>_def)
  ultimately show ?case
    by (simp add: Cons.IH H_assoc)
qed


(* TODO: the main theory is pending because of difficulty to get along with Isabelle's type system *)
theorem can_compose_SST_Transducer: 
  "SST.run (compose_SST_Transducer sst td) w1
 = (case SST.run sst w1 of
     Some(w2) \<Rightarrow> Transducer.run td w2 |
     None \<Rightarrow> None)"
apply (simp add: compose_SST_Transducer_def)
  sorry


thm compose_delta_hat

      
