(* Title:   Compose_SST_Transducer.thy
   Author:  Akama Hitoshi
*)

theory Compose_SST_Transducer
  imports Main List Option Update Transducer SST
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
  by (induction u arbitrary: q rule: xa_induct, simp_all)

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
         if Transducer.final td (\<Delta> (delta td) (f, \<lambda>x. u) (initial td, SOME x :: 'x1. True))
         then Some (H (delta td) (Transducer.eta td) (f, \<lambda>x. u)
                      (initial td, SOME x :: 'x1. True))
         else None |
       None \<Rightarrow> None)"

definition compose_SST_Transducer ::
  "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'b, 'c) transducer \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'a, 'c) SST" where
  "compose_SST_Transducer sst td = \<lparr>
    states  = states sst \<times> {f. \<forall>q2\<in>states td. \<forall>x1\<in>variables sst. f (q2, x1) \<in> states td},
    initial = (initial sst, \<lambda>(q2, x1). q2),
    delta   = compose_\<delta> sst td,
    variables = states td \<times> variables sst,
    eta     = compose_\<eta> sst td,
    final   = compose_final sst td
   \<rparr>"

lemma compose_\<delta>_hat: "hat1 (compose_\<delta> sst td) ((q, f), w) =
        (delta_hat sst (q, w),
         \<Delta> (delta td) (f, eta_hat sst (q, w)))"
proof (induction w arbitrary: q f)
  case Nil then show ?case by (simp add: idU_def \<Delta>_def)
next
  case (Cons a u) then show ?case by (simp add: compose_\<delta>_def \<Delta>_assoc)
qed

lemma compose_\<eta>_hat:
  "hat2 (compose_\<delta> sst td) (compose_\<eta> sst td) ((q, f), w) =
   H (delta td) (Transducer.eta td) (f, eta_hat sst (q, w))"
proof (induction w arbitrary: q f)
  case Nil then show ?case by (simp add: idU_def H_def)
next
  case (Cons a u) then show ?case by (simp add: compose_\<delta>_def compose_\<eta>_def H_assoc)
qed


subsection \<open>Property of valuation\<close>


lemma valuate_delta_hat_string: "hat1 (delta2f (\<lambda>(q, x). q) tr) (q, w) = hat1 tr (q, valuate w)"
  by (induction w arbitrary: q rule: xa_induct, simp_all add: empty_def)

lemma valuate_delta_hat: "hat1 tr (q, valuate (u x)) = \<Delta> tr (\<lambda>(q, x). q, u) (q, x)"
  by (simp add: comp_def \<Delta>_def valuate_delta_hat_string)

lemma valuate_eta_hat_string:
  "valuate (Transducer.hat2 (delta2f (\<lambda>(q2, x). q2) tr) (eta2f td) (q, w))
 = Transducer.hat2 tr td (q, valuate w)"
  by (induction w arbitrary: q rule: xa_induct, simp_all)

lemma valuate_eta_hat: "Transducer.hat2 tr td (q, valuate (u x)) = valuate (H tr td (\<lambda>(q, x). q, u) (q, x))"
  by (simp add: H_def valuate_eta_hat_string)


subsection \<open>Main results\<close>

lemma closed_delta2f: 
  assumes "closed_delta st var f"
  assumes "closed_delta st  al tr"
  shows "closed_delta st (var <+> al) (delta2f f tr)"
  unfolding closed_delta_def
proof (intro ballI)
  fix q ax
  assume q: "q \<in> st" and ax: "ax \<in> var <+> al"
  show "delta2f f tr (q, ax) \<in> st"
  proof (cases ax)
    case (Inl x)
    then have "x \<in> var" using ax by blast
    then have "f (q, x) \<in> st" by (meson assms(1) closed_delta_def q)
    then show ?thesis by (simp add: Inl)
  next
    case (Inr a)
    then have "a \<in> al" using ax by blast
    then have "tr (q, a) \<in> st" by (meson assms(2) closed_delta_def q)
    then show ?thesis by (simp add: Inr)
  qed
qed

lemma list_all_Plus_Inl:
  "list_all (\<lambda>a. a \<in> A <+> B) (map Inl u) = list_all (\<lambda>a. a \<in> A) u"
  by (induct u, auto)

lemma list_all_Plus_Inr:
  "list_all (\<lambda>a. a \<in> A <+> B) (map Inr u) = list_all (\<lambda>a. a \<in> B) u"
  by (induct u, auto)

lemma star_Inr [simp]: "map Inr u \<in> star (A <+> B) \<longleftrightarrow> u \<in> star B"
  by (simp add: star_def, rule list_all_Plus_Inr)

lemma star_UNIV [simp]: "star UNIV = UNIV"
  unfolding star_def
  using Ball_set by blast

lemma closed_eta2f:
  assumes "closed_delta st var f"
  assumes "closed_delta st al tr"
  assumes "q2 \<in> st"
  assumes "u \<in> star (var <+> al)"
  shows "Transducer.hat2 (delta2f f tr) (eta2f to) (q2, u) \<in> star (st \<times> var <+> UNIV)"
  using assms proof (induct u arbitrary: q2 rule: xa_induct)
  case Nil
  then show ?case by (simp add: star_def)
next
  case (Var x xs)
  then show ?case by (auto simp add: star_def closed_delta_def)
next
  case (Alpha a xs)
  assume q2: "q2 \<in> st"
  have a: "a \<in> al" by (insert Alpha.prems(4), auto simp add: star_def)
  have q': "tr (q2, a) \<in> st"
    apply (rule closed_delta_simp[of st al tr])
    by (simp_all add: assms q2 a)
  have xs: "xs \<in> star (var <+> al)"
    by (rule star_Cons[OF Alpha(5)])
  then show ?case
    apply (simp add: list_all_Plus_Inr list.pred_True)
    apply (rule star_append)
    apply (simp)
    apply (rule Alpha)
    using assms apply (simp_all add: q')
    done
qed
  
theorem compose_SST_Transducer_well_defined:
  assumes sst_well: "well_defined sst"
  assumes td_well:  "td_well_defined td"
  shows "well_defined (compose_SST_Transducer sst td)" (is "well_defined ?comp")
proof (auto)
  show "initial_in_states (states ?comp) (initial ?comp)"
    using sst_well unfolding well_defined_simps compose_SST_Transducer_def
    by simp
  show "closed_delta (states ?comp) UNIV (delta ?comp)"
    unfolding closed_delta_def compose_SST_Transducer_def compose_\<delta>_def \<Delta>_def
  proof (auto)
    fix q a
    assume "q \<in> states sst"
    then show "delta sst (q, a) \<in> states sst"
      using sst_well unfolding well_defined_simps
      by blast
  next
    fix f q1 a q2 x1
    assume q1: "q1 \<in> states sst"
    assume q2: "q2 \<in> states td"
    assume f: "\<forall>q2\<in>states td. \<forall>x1\<in>variables sst. f (q2, x1) \<in> states td"
    assume x1: "x1 \<in> variables sst"

    show "hat1 (delta2f f (delta td)) (q2, SST.eta sst (q1, a) x1) \<in> states td"
    proof (rule closed_delta_simp)
      have "closed_delta (states td) UNIV (delta td)"
      using td_well td_well_defined_def by auto
      moreover have "closed_delta (states td) (variables sst) f"
        using closed_delta_def f by blast
      ultimately have "closed_delta (states td) (variables sst <+> UNIV) (delta2f f (delta td))"
        by (simp add: closed_delta2f)
      then show delta2f_hat_closed:
        "closed_delta (states td) (star (variables sst <+> UNIV)) (hat1 (delta2f f (delta td)))"
        by (simp add: closed_delta_hat)
    next
      show "q2 \<in> states td" by (rule q2)
    next
      show "SST.eta sst (q1, a) x1 \<in> star (variables sst <+> UNIV)"
        apply (rule eta_closed_iff)
        by (auto simp add: sst_well q1 x1)
    qed
  qed
next
  show "closed_eta (compose_SST_Transducer sst td)"
    unfolding closed_eta_def compose_SST_Transducer_def compose_\<eta>_def H_def
  proof (auto)
    fix q1 f a q2 x1
    assume q1: "q1 \<in> states sst"
    assume q2: "q2 \<in> states td"
    assume f: "\<forall>q2\<in>states td. \<forall>x1\<in>variables sst. f (q2, x1) \<in> states td"
    assume x1: "x1 \<in> variables sst"
    have eta_hat_alphabet:
      "SST.eta sst (q1, a) x1 \<in> star (variables sst <+> UNIV)"
      apply (rule eta_closed_iff[OF _ q1 x1])
      by (auto simp add: sst_well)
    

  qed
next
  show "closed_final (compose_SST_Transducer sst td)"
    sorry
next

qed



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
    "valuate ((SST.eta_hat sst (initial sst, w) \<bullet> (\<lambda>x. output_final1)) (SOME x :: 'x. True))"
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
                       comp_ignore
                       valuate_eta_hat
                       H_assoc)
  qed
qed

end
