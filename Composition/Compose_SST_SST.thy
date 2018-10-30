(* Title:   Compose_SST_SST.thy
   Author:  Akama Hitoshi
*)

section \<open>Composition of SST and SST\<close>

theory Compose_SST_SST
  imports Main HOL.List HOL.Option "../Core/Update" "../Core/Transducer" "../Core/SST" "../Core/Monoid_SST"
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
              \<Rightarrow> ('q2, 'x1) trans \<times> ('z, 'x1, 'b) update' => ('q2 \<times> 'z, 'q2 \<times> 'x1, ('x2, 'c) update) update'"
  where "H tr to = (\<lambda>(f, \<theta>). (\<lambda>(q, a). Transducer.hat2 (delta2f f tr) (eta2f to) (q, \<theta> a)))"


proposition \<Delta>_assoc_string:
  "hat1 (delta2f (\<lambda>(q, a). hat1 (delta2f f tr) (q, theta a)) tr) (q, u) =
   hat1 (delta2f f tr) (q, hat_hom theta u)"
  by (induct u arbitrary: q rule: xa_induct, simp_all)

lemma \<Delta>_assoc: "\<Delta> t (f, \<phi> \<bullet> \<psi>) = \<Delta> t (\<Delta> t (f, \<phi>), \<psi>)"
  by (auto simp add: \<Delta>_def comp_def \<Delta>_assoc_string)

proposition H_assoc_string:
  "hat_hom (\<lambda>(q2, x1). Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (q2, theta x1))
     (Transducer.hat2 (delta2f (\<lambda>(q2, x1). hat1 (delta2f f t_trans) (q2, theta x1)) t_trans) (eta2f t_out) (q, u)) =
   Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (q, hat_hom theta u)"
  by (induct u arbitrary: q rule: xa_induct, simp_all add: Transducer.eta_append)

lemma H_assoc: "H tr to (f, \<phi> \<bullet> \<psi>) = H tr to (f, \<phi>) \<bullet> H tr to (\<Delta> tr (f, \<phi>), \<psi>)"
  by (auto simp add: \<Delta>_def H_def comp_def H_assoc_string)

subsection \<open>Construction\<close>

definition compose_\<delta> :: "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'x2, 'b, 'c) SST \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'a) trans" where
  "compose_\<delta> sst1 sst2 =
     (\<lambda>((q1, f), a). (delta sst1 (q1, a), \<Delta> (delta sst2) (f, SST.eta sst1 (q1, a))))"

definition compose_\<eta> :: "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'x2, 'b, 'c) SST \<Rightarrow>
                             ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'a, ('x2, 'c) update) updator" where
  "compose_\<eta> sst1 sst2 = (\<lambda>((q1, f), a). H (delta sst2) (eta sst2) (f, SST.eta sst1 (q1, a)))"

definition compose_final_update ::
  "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'x2, 'b, 'c) SST \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2) \<Rightarrow> ('q2 \<times> 'x1 + ('x2, 'c) update) list option)" where
  "compose_final_update sst1 sst2 = (\<lambda>(q1, f).
     case SST.final sst1 q1 of
       Some u \<Rightarrow> Some (H (delta sst2) (SST.eta sst2) (f, \<lambda>x. u)
                        (initial sst2, ())) |
       None \<Rightarrow> None)"

definition compose_final_string ::
  "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'x2, 'b, 'c) SST \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2) \<Rightarrow> ('x2 + 'c) list option)" where
  "compose_final_string sst1 sst2 = (\<lambda>(q1, f).
     case SST.final sst1 q1 of
       Some u \<Rightarrow> SST.final sst2 (\<Delta> (delta sst2) (f, \<lambda>x. u) (initial sst2, ())) |
       None \<Rightarrow> None)"

definition compose_SST_SST ::
  "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'x2, 'b, 'c) SST \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'x2, 'a, 'c) MSST" where
  "compose_SST_SST sst1 sst2 = \<lparr>
    initial = (initial sst1, \<lambda>(q2, x1). q2),
    delta   = compose_\<delta> sst1 sst2,
    eta     = compose_\<eta> sst1 sst2,
    final = compose_final_update sst1 sst2,
    final_string = compose_final_string sst1 sst2
   \<rparr>"

lemma compose_\<delta>_hat: "hat1 (compose_\<delta> sst1 sst2) ((q, f), w) =
        (delta_hat sst1 (q, w),
         \<Delta> (delta sst2) (f, SST.eta_hat sst1 (q, w)))"
proof (induct w arbitrary: q f)
  case Nil then show ?case by (simp add: idU_def \<Delta>_def)
next
  case (Cons a u) then show ?case by (simp add: compose_\<delta>_def \<Delta>_assoc)
qed

lemma compose_\<eta>_hat:
  "hat2 (compose_\<delta> sst1 sst2) (compose_\<eta> sst1 sst2) ((q, f), w) =
   H (delta sst2) (SST.eta sst2) (f, SST.eta_hat sst1 (q, w))"
proof (induct w arbitrary: q f)
  case Nil then show ?case by (simp add: idU_def H_def)
next
  case (Cons a u) then show ?case by (simp add: compose_\<delta>_def compose_\<eta>_def H_assoc)
qed


subsection \<open>Property of valuation\<close>

fun list_valuation :: "('x \<Rightarrow> 'a list) \<Rightarrow> ('x + 'a) list \<Rightarrow> 'a list" where
  "list_valuation \<mu> [] = []" |
  "list_valuation \<mu> (Inl x # w) = \<mu> x @ list_valuation \<mu> w" |
  "list_valuation \<mu> (Inr a # w) = a # list_valuation \<mu> w"


lemma valuation_delta_hat_string:
  assumes "\<forall>q x. delta_hat sst (q, \<mu> x) = f (q, x)"
  shows "delta_hat sst (q, list_valuation \<mu> u) = hat1 (delta2f f (delta sst)) (q, u)"
  using assms by (induct u arbitrary: q rule: xa_induct, simp_all) 

lemma valuation_delta_hat:
  assumes "\<forall>q x. hat1 (delta sst) (q, \<mu> x) = f (q, x)"
  shows "delta_hat sst (q, list_valuation \<mu> (\<theta> x)) = \<Delta> (delta sst) (f, \<theta>) (q, x)"
  by (simp add: \<Delta>_def valuation_delta_hat_string[OF assms])

lemma valuate_delta_hat_string: "hat1 (delta2f (\<lambda>(q, x). q) tr) (q, w) = hat1 tr (q, valuate w)"
  by (induct w arbitrary: q rule: xa_induct, simp_all add: empty_def)

lemma valuate_delta_hat: "hat1 tr (q, valuate (u x)) = \<Delta> tr (\<lambda>(q, x). q, u) (q, x)"
  by (simp add: comp_def \<Delta>_def valuate_delta_hat_string)


fun valuation_eta_hat ::  "('q, 'y, 'b, 'c, 'e) SST_scheme \<Rightarrow> ('x \<Rightarrow> 'b list) \<Rightarrow> 'q \<times> 'x \<Rightarrow> ('y, 'c) update list" where
  "valuation_eta_hat sst \<mu> (q, x) = [SST.eta_hat sst (q, \<mu> x)]"

lemma valuation_eta_hat_string:
  assumes "\<forall>q x. delta_hat sst (q, \<mu> x) = f (q, x)"
  shows "SST.eta_hat sst (q, list_valuation \<mu> u)
       = concatU (list_valuation (valuation_eta_hat sst \<mu>)
                                 (Transducer.hat2 (delta2f f (delta sst)) (eta2f (SST.eta sst)) (q, u)))"
 by (induct u arbitrary: q rule: xa_induct, simp_all add: eta_append assms)


lemma valuate_eta_hat_string:
  "concatU (valuate (Transducer.hat2 (delta2f (\<lambda>(q2, x). q2) tr) (eta2f td) (q, w)))
 = SST.hat2 tr td (q, valuate w)"
  by (induct w arbitrary: q rule: xa_induct, simp_all)

lemma valuate_eta_hat: "SST.hat2 tr td (q, valuate (u x)) = concatU (valuate (H tr td (\<lambda>(q, x). q, u) (q, x)))"
  by (simp add: H_def valuate_eta_hat_string)

lemmas valuate = valuate_delta_hat valuate_eta_hat


lemma reachable_then_exist_valuation:
  fixes sst1 :: "('q1, 'x1, 'a, 'b) SST"
  fixes sst2 :: "('q2, 'x2, 'b, 'c) SST"
  assumes "reachable (compose_SST_SST sst1 sst2) (q1, f)"
  shows "\<exists>\<mu>. \<forall>q2 x. delta_hat sst2 (q2, \<mu> x) = f (q2, x)"
proof -
  obtain w where w: "(q1, f) = delta_hat (compose_SST_SST sst1 sst2) (initial (compose_SST_SST sst1 sst2), w)"
    by (meson assms reachable_def)
  then show ?thesis proof (induct w arbitrary: q1 f rule: rev_induct)
    case Nil
    show ?case proof (rule exI, intro allI)
      fix q2 x
      let ?mu = "\<lambda>x1. []"
      show "delta_hat sst2 (q2, ?mu x) = f (q2, x)"
        using Nil unfolding compose_SST_SST_def by simp
    qed
  next
    case (snoc a w)
    show ?case proof -
      let ?q1f' = "delta_hat (compose_SST_SST sst1 sst2) (initial (compose_SST_SST sst1 sst2), w)"
      let ?q1' = "fst ?q1f'"
      let ?f' = "snd ?q1f'"
      have "(?q1', ?f') = delta_hat (compose_SST_SST sst1 sst2) (initial (compose_SST_SST sst1 sst2), w)" by simp
      then have "\<exists>\<mu>. \<forall>q2 x. delta_hat sst2 (q2, \<mu> x) = ?f' (q2, x)" by (rule snoc(1))
      then obtain \<mu>' where mu: "\<forall>q2 x. delta_hat sst2 (q2, \<mu>' x) = ?f' (q2, x)" by auto
      let ?mu = "\<lambda>x1. list_valuation \<mu>' (SST.eta sst1 (?q1', a) x1)"
      have body: "\<forall>q2 x1. delta_hat sst2 (q2, ?mu x1) = f (q2, x1)"
        using snoc(2) 
        apply (simp add: valuation_delta_hat[OF mu] compose_SST_SST_def compose_\<delta>_hat)
        apply (simp add: compose_\<delta>_def)
        done
      show ?thesis by (rule exI, rule body)
    qed
  qed
qed

subsection \<open>Main result\<close>

theorem can_compose_SST_SST:
  fixes sst1 :: "('q1, 'x1, 'a, 'b) SST"
  fixes sst2 :: "('q2, 'x2, 'b, 'c) SST"
  shows "Monoid_SST.run (compose_SST_SST sst1 sst2) w
       = Option.bind (SST.run sst1 w) (SST.run sst2)"
proof (cases "SST.final sst1 (delta_hat sst1 (initial sst1, w))")
  case None then show ?thesis
    by (simp add: compose_SST_SST_def SST.run_def Monoid_SST.run_def compose_final_update_def compose_\<delta>_hat)
next
  case Some_1: (Some output_final1)
  let ?output_of_1st_sst =
    "valuate ((SST.eta_hat sst1 (initial sst1, w) \<bullet> (\<lambda>x. output_final1)) ())"
  show ?thesis
  proof (cases "SST.final sst2 (delta_hat sst2 (initial sst2, ?output_of_1st_sst))")
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
                       Some_1)
  qed
qed

subsection \<open>Examples\<close>

lemma "Monoid_SST.run (compose_SST_SST rev rev) [1, 2, 3] = Some [1, 2, 3]"
  apply (simp add: compose_SST_SST_def compose_\<delta>_def compose_\<eta>_def compose_final_update_def compose_final_string_def
        Monoid_SST.run_def SST.run_def rev_def Update.comp_def hat_hom_def update2hom_def fold_sum_def idU_def emptyU_def)
  apply (simp add: \<Delta>_def H_def idU_def emptyU_def comp_def)
  done

end
