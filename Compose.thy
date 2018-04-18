(* Title:   Compose.thy
   Author:  Akama Hitoshi
*)

section \<open>Composition of two SSTs\<close>

theory Compose
  imports Main Compose_SST_SST Convert_Monoid_SST
begin


definition compose where
  "compose sst1 sst2 = convert_MSST (compose_SST_SST sst1 sst2)"


definition revrev where
  "revrev = compose_SST_SST rev rev"

definition revrevconv where
  "revrevconv = convert_MSST revrev"

lemma "SST.run revrevconv [0, 1, 2, 3, 4] = Some [0, 1, 2, 3, 4]"
  apply (simp add: SST.run_def
         revrevconv_def convert_MSST_def convert_\<delta>_def convert_\<eta>_def emptyU_def convert_final_def revrev_def
         compose_SST_SST_def compose_\<delta>_def compose_\<eta>_def compose_final_update_def compose_final_string_def
         comp_ignore rev_def H_def H'_def \<Delta>'_def \<Delta>_def comp_def \<tau>_def
         \<iota>_def \<iota>0_def synthesize_def map_alpha_def idS_def idU_def)
  done
