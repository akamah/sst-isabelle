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

definition run :: "('q, 'x, 'a, 'b) SST \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "run S as = (let q' = hat1 (delta S) (initial S, as) in
               let xi = hat2 (delta S) (eta S) (initial S, as)
               in case final S q' of
                 Some u => Some (valuate (hat_hom xi u)) |
                 None   => None)"


(* Combine two transition function (q \<times> x \<Rightarrow> q and q \<times> b \<Rightarrow> q) into 
  a new trans func
*)
fun delta2f ::
  "('q, 'x) trans => ('q, 'b) trans => ('q, 'x + 'b) trans" where
  "delta2f f g (q, Inl x) = f (q, x)" |
  "delta2f f g (q, Inr a) = g (q, a)"

(* eta2f is a function described in Akama's graduate thesis *)
fun eta2f :: 
  "('q, 'b, 'c) Transducer.out => ('q, 'x + 'b, 'q \<times> 'x + 'c) Transducer.out" where
  "eta2f e2 (q, Inl x) = [Inl (q, x)]" |
  "eta2f e2 (q, Inr a) = map Inr (e2 (q, a))"

abbreviation d2f :: "('q2, 'x1) trans => ('q2, 'b, 'c) transducer => ('q2, 'x1 + 'b) trans" where
  "d2f f T \<equiv> delta2f f (\<lambda>(q, a). Transducer.delta T (q, a))"

abbreviation e2f :: "('q, 'b, 'c) transducer => ('q, 'x + 'b, 'q \<times> 'x + 'c) Transducer.out" where
  "e2f T \<equiv> eta2f (\<lambda>(q, a). Transducer.eta T (q, a))"

lemma delta_append: "hat1 t (q, (as @ bs)) = hat1 t (hat1 t (q, as), bs)"
  by (induction as arbitrary: q, auto)

lemma eta_append: "hat2 tf to (q, as @ bs) = comp (hat2 tf to (q, as)) (hat2 tf to (hat1 tf (q, as), bs))"
  by (induction as arbitrary: q, auto simp add: comp_assoc comp_left_neutral)

lemma [simp]: "Transducer.hat1 d (q, w) = SST.hat1 d (q, w)"
proof (induction w arbitrary: q)
  case Nil
  show ?case by auto
next
  case (Cons a u)
  show ?case by (auto simp add: Cons)
qed

definition rev :: "(nat, nat, nat, nat) SST" where
  "rev = (|
    initial = 0, 
    delta = \<lambda>(q, a). 0,
    eta = \<lambda>(q, a) x. [Inr a, Inl 0],
    final = \<lambda>q. Some [Inl 0] |)"

lemma "run rev [2, 3, 4] = Some [4, 3, 2]"
  by (simp add: run_def rev_def Update.comp_def hat_hom_def update2hom_def fold_sum_def idU_def)

end
