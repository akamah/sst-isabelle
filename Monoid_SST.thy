(* Title:   Monoid_SST.thy
   Author:  Akama Hitoshi
*)

section \<open>Definition of Monoid SST\<close>

theory Monoid_SST
  imports Main Update SST
begin

record ('q, 'x, 'y, 'a, 'b) "MSST" =
  initial      :: "'q"
  delta        :: "('q, 'a) trans"
  eta          :: "('q, 'x, 'a, ('y, 'b) update) updator"
  final_update :: "'q \<Rightarrow> ('x + ('y, 'b) update) list option"
  final_string :: "'q \<Rightarrow> ('y + 'b) list option"

(* \<delta>\<^sup>^(q, w) *)
abbreviation delta_hat :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow> ('q, 'a list) trans" where
  "delta_hat msst \<equiv> hat1 (delta msst)"

(* \<eta>(q, w) *)
abbreviation eta_hat :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow> ('q, 'x, 'a list, ('y, 'b) update) updator" where
  "eta_hat msst \<equiv> hat2 (delta msst) (eta msst)"


definition run :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "run msst w = (case final_update msst (hat1 (delta msst) (initial msst, w)) of
      Some u \<Rightarrow> (case final_string msst (hat1 (delta msst) (initial msst, w)) of
         Some v \<Rightarrow> (let m = concatU ((valuate o (eta_hat msst (initial msst, w) \<bullet> (\<lambda>x. u))) (SOME x :: 'x. True))
                    in Some ((valuate o (m \<bullet> (\<lambda>y. v))) (SOME y :: 'y. True))) |
         None \<Rightarrow> None) |
      None \<Rightarrow> None)"

end
