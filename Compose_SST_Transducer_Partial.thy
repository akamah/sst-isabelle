theory Compose_SST_Transducer_Partial
  imports Main List Update Transducer SST
begin


(* This file includes a proof of SST-Transducer (partial) composition (in progress) 
   using NEW NOTATION (such as \<Delta>, H, ...) *)


definition remove_var :: "('x, 'b) update" where
  "remove_var x = []"

definition run_SST :: "('q, 'x, 'a, 'b) SST \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "run_SST sst w = (let q = SST.hat1 (delta sst) (initial sst, w)
                    in let \<xi> = SST.hat2 (delta sst) (eta sst) (initial sst, w)
                    in case final sst q of
                      Some u \<Rightarrow> Some (valuate ((remove_var \<bullet> \<xi> \<bullet> (\<lambda>x. u)) (SOME x :: 'x. True))) |
                      None \<Rightarrow> None)"

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
  "compose_\<delta> sst td = (\<lambda>((q1, f), a). (delta sst (q1, a),
                                         \<Delta> (Transducer.delta td) (f, eta sst (q1, a))))"
  
definition compose_\<eta> :: "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'a, 'c) update_f" where
  "compose_\<eta> sst td = (\<lambda>((q1, f), a). H (Transducer.delta td) (Transducer.eta td) (f, eta sst (q1, a)))"

definition compose_final :: "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2) \<Rightarrow> ('q2 \<times> 'x1 + 'c) list option)" where
  "compose_final sst td = (\<lambda>(q1, f). 
     case final sst q1 of
       Some u \<Rightarrow>
         if Transducer.final td (\<Delta> (Transducer.delta td) (f, \<lambda>x. u) (Transducer.initial td, q1))
         then Some (H (Transducer.delta td) (Transducer.eta td) (f, \<lambda>x. u) (Transducer.initial td, q1)) 
         else None |
       None \<Rightarrow> None)"


definition compose_SST_Transducer ::
  "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'a, 'c) SST" where
  "compose_SST_Transducer sst td = \<lparr>
    initial = (initial sst, \<lambda>(q2, x1) \<Rightarrow> q2),
    delta = compose_\<delta> sst td,
    eta = compose_\<eta> sst td,
    final = compose_final sst td
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


lemma initial_delta: "\<Delta> tr (\<lambda>(q, x). q, remove_var) = (\<lambda>(q, x). q)"
  by (simp add: \<Delta>_def remove_var_def)

lemma initial_eta: "H tr to (\<lambda>(q, x). q, remove_var) = remove_var"
  by (auto simp add: H_def remove_var_def)

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

definition all_alphabet :: "('x + 'b) list => bool" where
  "all_alphabet w = list_all (\<lambda>a. case a of Inr r => True | Inl l => False) w"

(* some predicate on hom *)
lemma list_all_hat_hom:
  assumes "list_all (\<lambda>ax. case ax of
                    Inl x => list_all pred (f x) |
                    Inr a => pred (Inr a)) w"
  shows "list_all pred (hat_hom f w)"
using assms proof (induction w)
  case Nil then show ?case by simp
next
  case (Cons a u)
  then show ?case by (cases a, auto)
qed


lemma all_alphabet_remove_var: "all_alphabet (remove_var x)"
by (simp add: all_alphabet_def remove_var_def)

lemma alphabet_remove_var: "all_alphabet (hat_hom remove_var w)"
  apply (unfold all_alphabet_def remove_var_def)
  apply (rule list_all_hat_hom)
  apply (simp add: rev_induct) (* by sledgehammer. why??? *)
  done

lemma valuate_delta_hat_string:
  assumes "all_alphabet w"
  shows "hat1 (delta2f f tr) (q, w) = hat1 tr (q, valuate w)"
using assms proof (induction w arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case
    by (cases a, auto simp add: all_alphabet_def valuate_distrib valuate_map)
qed

lemma valuate_delta_hat: "\<Delta> tr (f, remove_var \<bullet> u) (q, x) = hat1 tr (q, valuate ((remove_var \<bullet> u) x))"
  by (simp add: comp_def \<Delta>_def valuate_delta_hat_string alphabet_remove_var)


lemma valuate_eta_hat_string:
  assumes "all_alphabet w"
  shows "valuate (Transducer.hat2 (delta2f f tr) (eta2f td) (q, w)) = Transducer.hat2 tr td (q, valuate w)"
using assms proof (induction w arbitrary: q)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case
    by (cases a, auto simp add: all_alphabet_def valuate_distrib valuate_map)
qed

lemma valuate_eta_hat: "valuate (H tr td (f, remove_var \<bullet> u) (q, x)) = Transducer.hat2 tr td (q, valuate ((remove_var \<bullet> u) x))"
  by (simp add: comp_def H_def valuate_eta_hat_string alphabet_remove_var)

(*
lemma valuate_eta_hat_2:
  assumes "u = H tr td (\<lambda>(q, x). q, u') (q2_0, x)"
  shows "valuate u = Transducer.hat2 tr td (q2_0, valuate (u' x))"
  using assms by (simp add: valuate_eta_hat)
*)


declare [[show_types]]
theorem can_compose_SST_Transducer_total: 
  fixes sst::" ('q1, 'x, 'a, 'b) SST" and
        td::"('q2, 'b, 'c) transducer"
  shows
  "run_SST (compose_SST_Transducer sst td) w
 = (case run_SST sst w of
      Some v \<Rightarrow> Transducer.run td v |
      None \<Rightarrow> None)"
proof -
  let ?tr = "Transducer.delta td"
  let ?to = "Transducer.eta td"
  let ?H  = "H ?tr ?to"
  let ?f0 = "\<lambda>(q, x). q"
  let ?q' = "SST.hat1 (SST.delta sst) (SST.initial sst, w)"
  let ?xi = "SST.hat2 (SST.delta sst) (SST.eta sst) (SST.initial sst, w)"
(*
  have H_inner: "remove_var \<bullet> ?H (?f0, ?xi) \<bullet> ?H (\<Delta> ?tr (?f0, ?xi), SST2.final sst) 
               = ?H (?f0, remove_var \<bullet> ?xi \<bullet> SST2.final sst)"
    by (simp add: H_assoc initial_delta initial_eta)
  have H_swap: "\<And>\<psi> \<phi> q f x g. (\<psi> \<bullet> \<phi> \<bullet> (\<lambda>(q, f). ?H (f, g) (x, q))) (q, f) = (\<psi> \<bullet> \<phi> \<bullet> ?H (f, g)) (x, q)"
    by (simp add: comp_def)
*)
  show ?thesis
(*    apply (simp add: compose_SST_Transducer_def run_SST_def run_total_def) *)
  proof (cases "SST.final sst (SST.hat1 (SST.delta sst) (SST.initial sst, w))")
    case None
    then show ?thesis
      apply (simp add: compose_SST_Transducer_def run_SST_def)
      apply (simp add: Transducer.run_def compose_final_def compose_\<delta>_hat)
      done
  next
    case (Some a)
      let ?v = "valuate ((remove_var \<bullet> SST.hat2 (SST.delta sst) (SST.eta sst) (SST.initial sst, w) \<bullet> (\<lambda>x::'x. a)) (SOME x. True))"
      show ?thesis
        using Some
        apply (simp only: Transducer.run_def)
        apply (simp only: Let_def)
        apply (simp only: run_SST_def[of sst w])
        apply (simp only: Let_def option.simps)
      proof -
        show "run_SST (compose_SST_Transducer sst td) w =
              (if transducer.final td  (Transducer.hat1 (transducer.delta td) (transducer.initial td, ?v))
              then Some (Transducer.hat2 (transducer.delta td) (transducer.eta td) (transducer.initial td, ?v)) else None)"       
        proof (cases "transducer.final td (Transducer.hat1 (transducer.delta td) (transducer.initial td, ?v))")
          case True
          show ?thesis
          using True sorry (* proof (simp) *)
       next
         case False
         then show ?thesis
           using Some
         proof (simp add: compose_final_def compose_\<delta>_hat run_SST_def compose_SST_Transducer_def)

      
    qed


    apply (simp add: compose_final_def compose_\<delta>_hat compose_\<eta>_hat)
    apply (simp add: H_swap)
    apply (simp add: H_inner)
    apply (simp add: valuate_eta_hat remove_var_def)
    done
qed
