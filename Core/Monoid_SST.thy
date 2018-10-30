(* Title:   Monoid_SST.thy
   Author:  Akama Hitoshi
*)

section \<open>Definition of Monoid SST\<close>

theory Monoid_SST
  imports Main Update SST
begin

record ('q, 'x, 'y, 'a, 'b) "MSST" = "('q, 'x, 'a, ('y, 'b) update) SST" +
  final_string :: "'q \<Rightarrow> ('y + 'b) list option"

abbreviation final_update where
  "final_update \<equiv> final"


definition run :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "run msst w = (case SST.run msst w of
      Some u \<Rightarrow> (case final_string msst (hat1 (delta msst) (initial msst, w)) of
         Some v \<Rightarrow> Some ((valuate o (concatU u \<bullet> (\<lambda>y. v))) ()) |
         None \<Rightarrow> None) |
      None \<Rightarrow> None)"


end
