(* Title:   SST.thy
   Author:  Akama Hitoshi
*)

section \<open>The definition of streaming string transducers\<close>

theory SST
  imports Main Update Transducer
begin

(* type of transition function *)
type_synonym ('q, 'a)  "trans" =
  "'q \<times> 'a \<Rightarrow> 'q"

(* type of variable update function *)
type_synonym ('q, 'x, 'a, 'b) "updator" =
  "'q \<times> 'a \<Rightarrow> ('x, 'b) update"

record ('q, 'x, 'a, 'b) SST = 
  initial :: "'q"
  delta   :: "('q, 'a) trans"
  eta     :: "('q, 'x, 'a, 'b) updator"
  final   :: "'q \<Rightarrow> ('x + 'b) list option"

(* string input version of transition function *)
fun hat1 :: "('q, 'a) trans \<Rightarrow> ('q, 'a list) trans" where
  "hat1 t (q, [])     = q" |
  "hat1 t (q, (a#as)) = hat1 t (t (q, a), as)"

(* string input version of variable update function *)
fun hat2 :: "('q, 'a) trans \<Rightarrow> ('q, 'x, 'a, 'b) updator \<Rightarrow> ('q, 'x, 'a list, 'b) updator" where
  "hat2 t u (q, [])     = idU" |
  "hat2 t u (q, (a#as)) = u (q, a) \<bullet> hat2 t u (t (q, a), as)"

(* \<delta>\<^sup>\<star>(q, w) *)
abbreviation delta_hat :: "('q, 'x, 'a, 'b) SST \<Rightarrow> ('q, 'a list) trans" where
  "delta_hat sst \<equiv> hat1 (delta sst)"

(* \<delta>\<^sup>\<star>(q, w) *)
abbreviation eta_hat :: "('q, 'x, 'a, 'b) SST \<Rightarrow> ('q, 'x, 'a list, 'b) updator" where
  "eta_hat sst \<equiv> hat2 (delta sst) (eta sst)"

(* remove variables in the output string *)
fun valuate :: "('x + 'b) list => 'b list" where
  "valuate []           = []" |
  "valuate (Inl x#rest) = valuate rest" |
  "valuate (Inr b#rest) = b # valuate rest"

(* an initial variable assignment *)
definition empty :: "('x, 'b) update" where
  "empty x = []"

(* if the output is undefined, return None, or return some output *)
definition run :: "('q, 'x, 'a, 'b) SST \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "run sst w = (case final sst (delta_hat sst (initial sst, w)) of
      Some u \<Rightarrow> Some (valuate ((empty \<bullet> (eta_hat sst (initial sst, w) \<bullet> (\<lambda>x. u))) u)) |
      None   \<Rightarrow> None)"


subsection \<open>Lemmata\<close>

lemma delta_append: "hat1 t (q, (as @ bs)) = hat1 t (hat1 t (q, as), bs)"
  by (induction as arbitrary: q, auto)

lemma eta_append: "hat2 tf to (q, as @ bs) = hat2 tf to (q, as) \<bullet> hat2 tf to (hat1 tf (q, as), bs)"
  by (induction as arbitrary: q, auto simp add: comp_assoc comp_left_neutral)

lemma valuate_distrib: "valuate (as @ bs) == valuate as @ valuate bs"
proof (induction as)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case by (cases a, simp_all)
qed

lemma valuate_map: "valuate (map Inr as) = as"
  by (induction as, auto)

lemma [simp]: "Transducer.hat1 d (q, w) = SST.hat1 d (q, w)"
  by (induction w arbitrary: q, auto)


subsection \<open>Examples\<close>

definition rev :: "(nat, nat, nat, nat) SST" where
  "rev = (|
    initial = 0, 
    delta = \<lambda>(q, a). 0,
    eta = \<lambda>(q, a) x. [Inr a, Inl 0],
    final = \<lambda>q. Some [Inl 0] |)"

lemma "run rev [2, 3, 4] = Some [4, 3, 2]"
  by (simp add: run_def rev_def Update.comp_def hat_hom_def update2hom_def fold_sum_def idU_def empty_def)

end
