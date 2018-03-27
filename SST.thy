theory SST
  imports Main Update Transducer
begin

type_synonym ('q, 'a)  "trans" =
  "'q \<times> 'a \<Rightarrow> 'q"

type_synonym ('q, 'x, 'a, 'b) "updator" =
  "'q \<times> 'a \<Rightarrow> ('x, 'b) update"

record ('q, 'x, 'a, 'b) SST = 
  initial :: "'q"
  delta :: "('q, 'a) trans"
  eta :: "('q, 'x, 'a, 'b) updator"
  final :: "'q \<Rightarrow> ('x + 'b) list option"

fun hat1 :: "('q, 'a) trans \<Rightarrow> ('q, 'a list) trans" where
  "hat1 t (q, [])     = q" |
  "hat1 t (q, (a#as)) = hat1 t (t (q, a), as)"

fun hat2 :: "('q, 'a) trans \<Rightarrow> ('q, 'x, 'a, 'b) updator \<Rightarrow> ('q, 'x, 'a list, 'b) updator" where
  "hat2 t u (q, [])     = idU" |
  "hat2 t u (q, (a#as)) = u (q, a) \<bullet> hat2 t u (t (q, a), as)"

fun valuate :: "('x + 'b) list => 'b list" where
  "valuate []           = []" |
  "valuate (Inl x#rest) = valuate rest" |
  "valuate (Inr b#rest) = b # valuate rest"

fun remove_var :: "('x, 'b) update" where
  "remove_var x = []"

definition run :: "('q, 'x, 'a, 'b) SST \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "run sst w = (case final sst (SST.hat1 (delta sst) (initial sst, w)) of
      Some u \<Rightarrow> Some (valuate ((remove_var \<bullet> (SST.hat2 (delta sst) (eta sst) (initial sst, w) \<bullet> (\<lambda>x. u))) u)) |
      None   \<Rightarrow> None)"

lemma delta_append: "hat1 t (q, (as @ bs)) = hat1 t (hat1 t (q, as), bs)"
  by (induction as arbitrary: q, auto)

lemma eta_append: "hat2 tf to (q, as @ bs) = comp (hat2 tf to (q, as)) (hat2 tf to (hat1 tf (q, as), bs))"
  by (induction as arbitrary: q, auto simp add: comp_assoc comp_left_neutral)

lemma [simp]: "Transducer.hat1 d (q, w) = SST.hat1 d (q, w)"
  by (induction w arbitrary: q, auto)

definition rev :: "(nat, nat, nat, nat) SST" where
  "rev = (|
    initial = 0, 
    delta = \<lambda>(q, a). 0,
    eta = \<lambda>(q, a) x. [Inr a, Inl 0],
    final = \<lambda>q. Some [Inl 0] |)"

lemma "run rev [2, 3, 4] = Some [4, 3, 2]"
  by (simp add: run_def rev_def Update.comp_def hat_hom_def update2hom_def fold_sum_def idU_def)

end
