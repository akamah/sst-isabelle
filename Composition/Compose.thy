(* Title:   Compose.thy
   Author:  Akama Hitoshi
*)

section \<open>Composition of two SSTs\<close>

theory Compose
  imports Main Compose_SST_SST Convert_Monoid_SST
begin


definition compose where
  "compose sst1 sst2 = convert_MSST (compose_SST_SST sst1 sst2)"


theorem SST_can_compose:
  "SST.run (compose sst1 sst2) w = Option.bind (SST.run sst1 w) (SST.run sst2)"
  by (simp add: compose_def MSST_can_convert  can_compose_SST_SST)

definition revrev where
  "revrev = compose_SST_SST rev rev"

definition revrevconv where
  "revrevconv = convert_MSST revrev"

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
  then show ?thesis unfolding SST.run_def SST_run_def by (simp add: comp_apply)
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

definition revresetconv where
  "revresetconv = convert_MSST revreset"

value "SST_run rev [1, 2, 3]"

lemmas runner = SST.run_def Monoid_SST.run_def
         convert_MSST_def convert_\<delta>_def convert_\<eta>_def emptyU_def convert_final_def
         compose_SST_SST_def compose_\<delta>_def compose_\<eta>_def compose_final_update_def compose_final_string_def
         comp_ignore rev_def H_def H'_def \<Delta>'_def \<Delta>_def comp_def
         \<iota>_def synthesize_def synthesize_shuffle_def synthesize_store_def 
         resolve_shuffle_def map_alpha_def idS_def idU_def \<alpha>0_def padding_def resolve_store_def scan_def

lemma "Monoid_SST.run revreset [1, 2, 0, 1, 2, 3] = Some [2, 1]"
  by (simp add: runner revreset_def revresetconv_def reset_def)

lemma "SST.run revresetconv [1, 0, 0, 1, 2, 0, 1, 2, 3, 0] = Some [1]"
  by (simp add: runner revreset_def revresetconv_def reset_def)


lemma "SST.run revrevconv [0] = Some [0]"
  by (simp add: runner revrevconv_def revrev_def)

