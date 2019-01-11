(* Title:   Compose.thy
   Author:  Akama Hitoshi
*)

section \<open>Composition of two SSTs\<close>

theory Compose
  imports Main Compose_SST_SST Convert_Monoid_SST
          "../Type/Compose_SST_SST_Type" "../Bounded_Copy/Bounded_Copy_SST_SST" "../Type/Compose_SST_SST_Type" "../Bounded_Copy/Bounded_Copy_Convert"
begin


abbreviation compose where
  "compose B sst1 sst2 \<equiv> convert_MSST B (compose_SST_SST sst1 sst2)"


theorem SST_can_compose:
  assumes "boundedness B k"
  assumes "bounded_copy_SST k sst2"
  assumes "trim sst2" (* without loss of generality, we can assume sst2 is trim *)
  shows "SST.run (compose B sst1 sst2) w = Option.bind (SST.run sst1 w) (SST.run sst2)"
proof -
  let ?gm = "compose_\<gamma> sst1 sst2"
  let ?comp = "compose_SST_SST sst1 sst2"
  have "bctype k ?comp ?gm" by (simp add: compose_typable assms)
  then show ?thesis unfolding compose_def using assms
    by (simp add: MSST_can_convert can_compose_SST_SST)
qed

theorem composed_SST_bounded:
  fixes sst1 :: "('q1::enum, 'x1::enum, 'a, 'b) SST"
  fixes sst2 :: "('q2::enum, 'x2::enum, 'b, 'c) SST"
  fixes B1 :: "'e1::enum boundedness"
  fixes B2 :: "'e2::enum boundedness"
  assumes "boundedness B1 k"
  assumes "boundedness B2 l"
  assumes "bounded_copy_SST k sst1"
  assumes "bounded_copy_SST l sst2"
  assumes "trim sst2"
  shows "bounded_copy_SST (card (UNIV::'q2 set) * k * l) (compose B2 sst1 sst2)"
proof -
  let ?msst = "compose_SST_SST sst1 sst2"
  let ?gamma = "compose_\<gamma> sst1 sst2"
  let ?Bq2_k = "Type_Nat :: ('q2 \<times> 'e1) type_nat"
  let ?q2_k = "card (UNIV::'q2 set) * k"
  have bound: "boundedness ?Bq2_k ?q2_k"
    using assms(1)
    unfolding boundedness_def by (simp add: card_UNIV_length_enum[symmetric] UNIV_Times_UNIV[symmetric] del: UNIV_Times_UNIV)
  have bc_msst: "bounded_copy_SST ?q2_k ?msst"
    by (simp add: compose_SST_SST_bounded assms(3))
  have bc_type: "bctype l ?msst ?gamma"
    by (simp add: compose_typable assms(4-5))
  show ?thesis
    by (rule convert_MSST_bounded[OF bc_msst bound assms(2) bc_type])
qed

definition revrev where
  "revrev = compose_SST_SST rev rev"

definition SST_run :: "('q, 'x, 'a, 'b) SST \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "SST_run sst w = (case SST.final sst (delta_hat sst (initial sst, w)) of
      Some u \<Rightarrow> Some ((valuate o (SST.eta_hat sst (initial sst, w) \<bullet> (\<lambda>x :: nat. u))) 0) |
      None   \<Rightarrow> None)"

lemma "SST.run sst w = SST_run sst w"
proof (cases "SST.final sst (delta_hat sst (initial sst, w))")
  case None
  then show ?thesis unfolding SST.run_def SST_run_def by simp
next
  case (Some a)
  then show ?thesis unfolding SST.run_def SST_run_def by (simp add: compU_apply)
qed

definition MSST_run :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "MSST_run msst w = (case final_update msst (hat1 (delta msst) (initial msst, w)) of
      Some u \<Rightarrow> (case final_string msst (hat1 (delta msst) (initial msst, w)) of
         Some v \<Rightarrow> (let m = concatU ((valuate o (eta_hat msst (initial msst, w) \<bullet> (\<lambda>x. u))) (0 :: nat))
                    in Some ((valuate o (m \<bullet> (\<lambda>y. v))) (0 :: nat))) |
         None \<Rightarrow> None) |
      None \<Rightarrow> None)"

definition revreset where
  "revreset = compose_SST_SST rev reset"

value "SST_run rev [1, 2, 3]"


end
