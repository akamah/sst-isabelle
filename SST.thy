theory SST
  imports Main Update Transducer
begin

(* type of alphabet + variable will be 'x + 'a *)

type_synonym ('q, 'a) "trans_f" =
  "'q \<times> 'a \<Rightarrow> 'q"
  
type_synonym ('q, 'a, 'b) "trans_out" =
  "'q \<times> 'a \<Rightarrow> 'b list"

type_synonym ('q, 'x, 'a, 'b) "update_f" =
  "'q \<times> 'a \<Rightarrow> ('x, 'b) update"


record ('q, 'x, 'a, 'b) SST = 
  initial :: "'q"
  delta :: "('q, 'a) trans_f"
  eta :: "('q, 'x, 'a, 'b) update_f"
  final :: "'q \<Rightarrow> ('x + 'b) list option"



fun hat1 :: "('q, 'a) trans_f \<Rightarrow> ('q, 'a list) trans_f" where
  "hat1 t (q, [])     = q" |
  "hat1 t (q, (a#as)) = hat1 t (t (q, a), as)"


fun hat2 :: "('q, 'a) trans_f \<Rightarrow> ('q, 'x, 'a, 'b) update_f \<Rightarrow> ('q, 'x, 'a list, 'b) update_f" where
  "hat2 t u (q, [])     = idU" |
  "hat2 t u (q, (a#as)) = comp (u (q, a)) (hat2 t u (t (q, a), as))"


fun valuate :: "('x + 'b) list => 'b list" where
  "valuate []           = []" |
  "valuate (Inl x#rest) = valuate rest" |
  "valuate (Inr b#rest) = b # valuate rest"

(*
definition delta_hat :: "('q, 'x, 'a, 'b) SST => ('q, 'a list) trans_f" where
  "delta_hat \<equiv> hat1 o delta"

declare delta_hat_def [simp]

definition eta_hat :: "('q, 'x, 'a, 'b) SST => ('q, 'x, 'a list, 'b) update_f" where
  "eta_hat T \<equiv> hat2 (delta T) (eta T)"

declare eta_hat_def [simp]
*)

definition run :: "('q, 'x, 'a, 'b) SST \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "run S as = (let q' = hat1 (delta S) (initial S, as) in
               let xi = hat2 (delta S) (eta S) (initial S, as)
               in case final S q' of
                 Some u => Some (valuate (hat_hom xi u)) |
                 None   => None)"


fun delta2f ::
  "('q, 'x) trans_f => ('q, 'b) trans_f => ('q, 'x + 'b) trans_f" where
  "delta2f f g (q, Inl x) = f (q, x)" |
  "delta2f f g (q, Inr a) = g (q, a)"


fun eta2f :: 
  "('q, 'b, 'c) trans_out => ('q, 'x + 'b, 'q \<times> 'x + 'c) trans_out" where
  "eta2f e2 (q, Inl x) = [Inl (q, x)]" |
  "eta2f e2 (q, Inr a) = map Inr (e2 (q, a))"


abbreviation d2f :: "('q2, 'x1) trans_f => ('q2, 'b, 'c) transducer => ('q2, 'x1 + 'b) trans_f" where
  "d2f f T \<equiv> delta2f f (\<lambda>(q, a). Transducer.delta T (q, a))"

abbreviation e2f :: "('q, 'b, 'c) transducer => ('q, 'x + 'b, 'q \<times> 'x + 'c) trans_out" where
  "e2f T \<equiv> eta2f (\<lambda>(q, a). Transducer.eta T (q, a))"

definition compose_delta ::
  "('q1, 'x1, 'a, 'b) SST => ('q2, 'b, 'c) transducer => ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'a) trans_f" where
  "compose_delta S1 T2 =
     (\<lambda>((q1, f), a). (delta S1 (q1, a), \<lambda>(q2, x1). hat1 (d2f f T2) (q2, eta S1 (q1, a) x1)))"

definition compose_eta :: 
  "('q1, 'x1, 'a, 'b) SST => ('q2, 'b, 'c) transducer => 
   ('q1 \<times> ('q2 \<times> 'x1 => 'q2), 'q2 \<times> 'x1, 'a, 'c) update_f" where
  "compose_eta S1 T2 = (\<lambda>((q1, f), a) (q2, x1). 
    Transducer.hat2 (d2f f T2) (e2f T2) (q2, eta S1 (q1, a) x1))"

definition compose_final :: 
  "('q1, 'x1, 'a, 'b) SST => ('q2, 'b, 'c) transducer =>
   ('q1 \<times> ('q2 \<times> 'x1 => 'q2) => ('q2 \<times> 'x1 + 'c) list option)" where
  "compose_final S1 T2 = (\<lambda>(q1, f). (case final S1 q1 of
    Some u => if Transducer.final T2 (hat1 (d2f f T2) (Transducer.initial T2, u))
              then Some (Transducer.hat2 (d2f f T2) (e2f T2) (Transducer.initial T2, u))
              else None |
    None => None))"


definition compose ::
  "('q1, 'x1, 'a, 'b) SST => ('q2, 'b, 'c) transducer =>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'a, 'c) SST" where
  "compose S1 T2 = (|
    initial = (initial S1, \<lambda>(q2, _). q2),
    delta = compose_delta S1 T2,
    eta = compose_eta S1 T2,
    final = compose_final S1 T2
  |)"



(* f'(q, x) = delta^2_f(q, theta(x)) *)
definition delta2f_apply :: "('q, 'x) trans => ('q, 'b) trans => ('x, 'b) update => ('q, 'x) trans" where
  "delta2f_apply f t theta = (\<lambda>(q2, x1). hat1 (delta2f f t) (q2, theta x1))"

(* g'(q, x) = eta^2_f(q, theta(x)) *)
definition eta2f_apply :: 
  "('q, 'x) trans => ('q, 'b) trans => ('q, 'b, 'c) Transducer.out => ('x, 'b) update => ('q, 'x, ('q \<times> 'x) + 'c) trans_out" where
  "eta2f_apply f t_trans t_out theta = (\<lambda>(q2, x1). Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (q2, theta x1))"

definition hat1_delta2f_delta2f_apply :: "('q, 'x) trans \<Rightarrow> ('q, 'b) trans \<Rightarrow> ('x, 'b) update \<Rightarrow> ('q, ('x + 'b) list) trans" where
  "hat1_delta2f_delta2f_apply f t theta = hat1 (delta2f (delta2f_apply f t theta) t)"


(* TODO: change q \<Rightarrow> x \<Rightarrow> q to q \<times> x \<Rightarrow> q in the definition of transition 
  ... DONE *)
definition hat2_eta2f_eta2f_apply :: "('q, 'x) trans \<Rightarrow> ('q, 'b) trans \<Rightarrow> ('q, 'b, 'c) trans_out \<Rightarrow> ('x, 'b) update \<Rightarrow>
                                      ('q, ('x + 'b) list, ('q \<times> 'x) + 'c) trans_out" where
  "hat2_eta2f_eta2f_apply f t_trans t_out theta = Transducer.hat2 (delta2f (delta2f_apply f t_trans theta) t_trans) (eta2f t_out)"



lemma delta_append: "hat1 t (q, (as @ bs)) = hat1 t (hat1 t (q, as), bs)"
  by (induction as arbitrary: q, auto)

lemma eta_append: "hat2 tf to (q, as @ bs) = comp (hat2 tf to (q, as)) (hat2 tf to (hat1 tf (q, as), bs))"
  by (induction as arbitrary: q, auto simp add: comp_assoc comp_left_neutral)



proposition delta2f_apply_hat: 
  "hat1 (delta2f (delta2f_apply f tr theta) tr) (q, u) =
   hat1 (delta2f f tr) (q, hat_hom theta u)"
proof (induction u arbitrary: q)
  case Nil
    show ?case by auto
next
  let ?f' = "delta2f_apply f tr theta"
  fix xORa axs
  case (Cons ax v)
  show ?case
  proof (cases ax)
    fix x assume asm: "ax = Inl x"
    hence "hat1 (delta2f ?f' tr) (q, ax#v) = hat1 (delta2f ?f' tr) (?f' (q, x), v)"
      by (simp)
    also have "... = hat1 (delta2f f tr) (?f' (q, x), hat_hom theta v)"
      by (simp add: Cons)
    also have "... = hat1 (delta2f f tr) (q, theta x @ hat_hom theta v)"
      by (simp add: delta2f_apply_def delta_append)
    also have "... = hat1 (delta2f f tr) (q, hat_hom theta (Inl x # v))" by auto
    also have "... = hat1 (delta2f f tr) (q, hat_hom theta (ax # v))" by (simp add: asm)
    finally show "?thesis" .
  next
    fix a assume asm: "ax = Inr a"
    hence "hat1 (delta2f ?f' tr) (q, ax#v) = hat1 (delta2f ?f' tr) (tr (q, a), v)"
      by (simp)
    also have "... = hat1 (delta2f f tr) (tr (q, a), hat_hom theta v)"
      by (simp add: Cons)
    also have "... = hat1 (delta2f f tr) (q, Inr a # hat_hom theta v)"
      by (simp)
    also have "... = hat1 (delta2f f tr) (q, hat_hom theta (Inr a # v))" by auto
    also have "... = hat1 (delta2f f tr) (q, hat_hom theta (ax # v))" by (simp add: asm)
    finally show "?thesis" .
  qed
qed

lemma [simp]: "Transducer.hat1 d (q, w) = SST.hat1 d (q, w)"
proof (induction w arbitrary: q)
  case Nil
  show ?case by auto
next
  case (Cons a u)
  show ?case by (auto simp add: Cons)
qed


proposition eta2f_apply_hat:
  "hat_hom (eta2f_apply f t_trans t_out theta) (Transducer.hat2 (delta2f (delta2f_apply f t_trans theta) t_trans) (eta2f t_out) (q, u)) =
   Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (q, hat_hom theta u)"
proof (induction u arbitrary: q)
  case Nil
  show ?case by auto
next
  let ?f' = "delta2f_apply f t_trans theta"
  let ?g' = "eta2f_apply f t_trans t_out theta"
  fix xORa axs
  case (Cons ax v)
  show ?case
  proof (cases ax)
    fix x assume asm: "ax = Inl x"
    hence "hat_hom ?g' (Transducer.hat2 (delta2f ?f' t_trans) (eta2f t_out) (q, ax#v)) 
         = hat_hom ?g' (Inl (q, x) # Transducer.hat2 (delta2f ?f' t_trans) (eta2f t_out) (?f' (q, x), v))" by (simp)
    also have "... = ?g' (q, x) @ hat_hom ?g' (Transducer.hat2 (delta2f ?f' t_trans) (eta2f t_out) (?f' (q, x), v))" by (simp)
    also have "... = ?g' (q, x) @ Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (?f' (q, x), hat_hom theta v)"
      by (simp add: Cons)
    also have "... = Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (q, hat_hom theta [Inl x]) @
                     Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (?f' (q, x), hat_hom theta v)"
      by (simp add: eta2f_apply_def)
    also have "... = Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (q, hat_hom theta (ax # v))"
      by (auto simp add: Transducer.eta_append delta2f_apply_def asm)
    finally show ?thesis .
  next
    fix a assume asm: "ax = Inr a"
    hence "hat_hom ?g' (Transducer.hat2 (delta2f ?f' t_trans) (eta2f t_out) (q, ax#v)) 
         = hat_hom ?g' (eta2f t_out (q, Inr a) @ Transducer.hat2 (delta2f ?f' t_trans) (eta2f t_out) (t_trans (q, a), v))" by (simp)
    also have "... = hat_hom ?g' (eta2f t_out (q, Inr a)) @ hat_hom ?g' (Transducer.hat2 (delta2f ?f' t_trans) (eta2f t_out) (t_trans (q, a), v))" by (simp)
    also have "... = hat_hom ?g' (eta2f t_out (q, Inr a)) @ Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (t_trans (q, a), hat_hom theta v)" by (simp add: Cons)
    also have "... = eta2f t_out (q, ax) @ Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (t_trans (q, a), hat_hom theta v)"
      by (simp add: hat_hom_right_ignore asm)
    also have "... = Transducer.hat2 (delta2f f t_trans) (eta2f t_out) (q, hat_hom theta (ax # v))" by (auto simp add: asm)
    finally show ?thesis .
  qed
qed
 
lemma compose_delta_hat: "hat1 (compose_delta sst transducer) ((q1, f), w) = 
         (hat1 (delta sst) (q1, w), delta2f_apply f (Transducer.delta transducer) (SST.hat2 (delta sst) (eta sst) (q1, w)))"
proof (induction w arbitrary: q1 f)
  case Nil
  show ?case by (simp add: delta2f_apply_def idU_def)
next
  fix a u
  case (Cons a u)
  let ?q1'  = "SST.delta sst (q1, a)"
  let ?tr = "Transducer.delta transducer"
  let ?f'  = "delta2f_apply f ?tr (SST.eta sst (q1, a))"
  let ?f'' = "delta2f_apply ?f' ?tr (SST.hat2 (delta sst) (eta sst) (?q1', u))"
  let ?f'''= "delta2f_apply f ?tr (SST.hat2 (delta sst) (eta sst) (q1, a # u))"
  have "hat1 (compose_delta sst transducer) ((q1, f), a # u) =
          (hat1 (compose_delta sst transducer) ((?q1', ?f'), u))" by (simp add: compose_delta_def delta2f_apply_def)
  also have "... = (hat1 (delta sst) (q1, a # u), ?f'')" by (simp add: Cons)
  also have "... = (hat1 (delta sst) (q1, a # u), ?f''')" proof -
    have "\<And>q2 x1. ?f'' (q2, x1) = ?f''' (q2, x1)" proof -
      fix q2 x1
      let ?u' = "SST.hat2 (SST.delta sst) (SST.eta sst) (SST.delta sst (q1, a), u) x1"
      have "SST.hat1 (delta2f (delta2f_apply f ?tr (SST.eta sst (q1, a))) ?tr) (q2, ?u')
            = SST.hat1 (delta2f f ?tr) (q2, hat_hom (SST.eta sst (q1, a)) ?u')" by (simp add: delta2f_apply_hat)
      thus "?f'' (q2, x1) = ?f''' (q2, x1)" by (simp add: delta2f_apply_def Update.comp_def)
    qed
    then show "(hat1 (delta sst) (q1, a # u), ?f'') = (hat1 (delta sst) (q1, a # u), ?f''')" by auto
  qed
  finally show ?case .
qed


lemma compose_eta_hat: "hat2 (compose_delta sst transducer) (compose_eta sst transducer) ((q1, f), w) (q2, x1) = 
         eta2f_apply f (Transducer.delta transducer) (Transducer.eta transducer) (SST.hat2 (delta sst) (eta sst) (q1, w)) (q2, x1)"
proof (induction w arbitrary: q1 f q2 x1)
  case Nil
  then show ?case by (simp add: eta2f_apply_def idU_def)
next
  case (Cons a u)
  let ?tr = "Transducer.delta transducer"
  let ?to = "Transducer.eta transducer"
  let ?f'  = "delta2f_apply f ?tr (SST.eta sst (q1, a))"
  let ?g'  = "eta2f_apply f ?tr ?to (SST.eta sst (q1, a))"
  let ?cd = "compose_delta sst transducer"
  let ?ce = "compose_eta sst transducer"
  let ?q1' = "SST.delta sst (q1, a)"
  let ?u   = "SST.hat2 (SST.delta sst) (SST.eta sst) (?q1', u) x1"
  let ?\<theta>  = "SST.eta sst (q1, a)"
  have "hat2 ?cd ?ce ((q1, f), a # u) (q2, x1) = hat_hom (?ce ((q1, f), a)) (hat2 ?cd ?ce (?cd ((q1, f), a), u) (q2, x1))"
    by (simp add: compose_delta_def compose_eta_def comp_def)
  also have "... = hat_hom (eta2f_apply f ?tr ?to (SST.eta sst (q1, a))) (hat2 ?cd ?ce ((?q1', ?f'), u) (q2, x1))"
    by (simp add: delta2f_apply_def eta2f_apply_def compose_eta_def compose_delta_def)
  also have "... = hat_hom (eta2f_apply f ?tr ?to (SST.eta sst (q1, a)))
                    (eta2f_apply ?f' ?tr ?to (SST.hat2 (delta sst) (eta sst) (?q1', u)) (q2, x1))"
    by (simp add: Cons) 
  also have "... = hat_hom (eta2f_apply f ?tr ?to (SST.eta sst (q1, a)))
                    (Transducer.hat2 (delta2f ?f' ?tr) (eta2f ?to) (q2, ?u))"
    by (simp add: delta2f_apply_def eta2f_apply_def)
  also have "... = Transducer.hat2 (delta2f f ?tr) (eta2f ?to) (q2, hat_hom ?\<theta> ?u)"
    by (rule eta2f_apply_hat)
  also have "... = Transducer.hat2 (delta2f f ?tr) (eta2f ?to) (q2, SST.hat2 (SST.delta sst) (SST.eta sst) (q1, a # u) x1)"
    by (auto simp add: Update.comp_def)
  finally show ?case by (simp add: eta2f_apply_def)
qed

thm compose_delta_hat
thm compose_eta_hat




definition trans_apply :: "('q, 'b) trans => ('a => 'b list) => ('q, 'a) trans" 
where "trans_apply \<delta> \<theta> = (\<lambda>q a. hat1 \<delta> q (\<theta> a))"

definition out_apply :: "('q, 'b) trans => ('q, 'b, 'c) out => ('a => 'b list) => ('q, 'a, 'c) out" where
  "out_apply \<delta> \<eta> \<theta> = (\<lambda>q a. Transducer.hat2 \<delta> \<eta> q (\<theta> a))"

definition to_hom :: "('a => 'a list) => ('a list => 'a list)" where
  "to_hom f = (\<lambda>as. concat (map f as))"

definition hom_id :: "'a => 'a list" where
  "hom_id a = [a]"

definition hom_comp :: "('a => 'a list) => ('a => 'a list) => ('a => 'a list)" where
  "hom_comp f g a = to_hom f (g a)"


lemma [simp]: "to_hom f [] = []"
  by (simp add: to_hom_def)   

lemma [simp]: "to_hom f (x#xs) = f x @ to_hom f xs"
  by (simp add: to_hom_def)

lemma [simp]: "to_hom f (xs@ys) = to_hom f xs @ to_hom f ys"
  by (simp add: to_hom_def)


lemma [simp]: "trans_apply \<delta> hom_id = \<delta>"
  by (simp add: hom_id_def trans_apply_def)

lemma trans_apply_hom: "hat1 (trans_apply \<delta> \<theta>) q w = hat1 \<delta> q (to_hom \<theta> w)"
  by (induction w arbitrary: q, auto simp add: delta_append trans_apply_def)
 
lemma "trans_apply (trans_apply \<delta> \<theta>) \<tau> q a = trans_apply \<delta> (hom_comp \<theta> \<tau>) q a"
proof -
  have "trans_apply (trans_apply \<delta> \<theta>) \<tau> q a = hat1 (trans_apply \<delta> \<theta>) q (\<tau> a)"
    by (simp add: trans_apply_def)
  also have "... = hat1 \<delta> q (to_hom \<theta> (\<tau> a))"
    by (simp add: trans_apply_hom)
  also have "... = trans_apply \<delta> (hom_comp \<theta> \<tau>) q a"
    by (simp add: hom_comp_def trans_apply_def)
  finally show ?thesis .
qed

lemma out_apply_hom: "Transducer.hat2 (trans_apply \<delta> \<theta>) (out_apply \<delta> \<eta> \<theta>) q w =
                      Transducer.hat2 \<delta> \<eta> q (to_hom \<theta> w)"
  by (induction w arbitrary: q, auto simp add: Transducer.eta_append trans_apply_def out_apply_def)

lemma [simp]: "out_apply \<delta> \<eta> hom_id = \<eta>"
  by (auto simp add: out_apply_def hom_id_def)


definition compose_SST_delta ::
  "('q2, 'b, 'c) transducer => ('q1, 'x1, 'a, 'b) SST =>
   ('q1 \<times> ('q2 => 'x1 => 'q2), 'a) trans" where
  "compose_SST_delta T2 S1 =
    (\<lambda>(q1, f) a. (delta S1 q1 a, 
                  trans_apply (delta2f f (Transducer.delta T2)) (eta S1 q1 a))) "

lemma trans_apply_idU: "trans_apply (d2f f T2) idU = f"
  by (simp add: idU_def trans_apply_def delta2f_def)


(*
lemma trans_apply_sum: 
  "delta2f (trans_apply (delta2f f \<delta>) \<theta>) \<delta> = trans_apply (delta2f f \<delta>) \<theta>"

lemma compose_SST_delta_hat:
  "hat1 (compose_SST_delta T2 S1) (q, f) w =
   (hat1 (delta S1) q w, trans_apply (d2f f T2) (hat2 (delta1 S1) (delta2 S1) q w))"
  apply (induction w arbitrary: q f)
  apply (auto simp add: compose_SST_delta_def trans_apply_idU)
  
*)

(*
lemma "hat1 (delta2f (delta2f_apply f tr theta) tr) q u = hat1 (delta2f f tr) q (hat_hom theta u)"
proof (induction u arbitrary: q)
  case Nil
    show ?case by auto
next
  let ?f' = "delta2f_apply f tr theta"
  fix xORa axs
  case (Cons ax v)
  show ?case
  proof (cases ax)
    fix x assume asm: "ax = Inl x"
    hence "hat1 (delta2f ?f' tr) q (ax#v) = hat1 (delta2f f tr) (?f' q x) (hat_hom theta v)"
      proof (auto simp add: Cons.IH)
        thm Cons.IH
    also have "... = hat1 (delta2f f tr) q (hat_hom theta (ax # v))" 
      by (simp add: delta2f_apply_def delta_append asm)
    finally show "?thesis" by simp
  next
    fix a assume asm: "ax = Inr a"
    hence "hat1 (delta2f ?f' tr) q (ax#v) = hat1 (delta2f ?f' tr) (tr q a) v"
      by (simp add: delta2f_def)
    also have "... = hat1 (delta2f f tr) (tr q a) (hat_hom theta v)"
      by (simp add: Cons)
    also have "... = hat1 (delta2f f tr) q (hat_hom theta (ax # v))"
      by (simp add: delta2f_def asm)
    finally show "?thesis" by simp
  qed
qed
*)



definition rev :: "(nat, nat, nat, nat) SST" where
  "rev = (|
    initial = 0, 
    delta = \<lambda>q a. 0,
    eta = \<lambda>q a x. [Inr a, Inl 0],
    final = \<lambda>q. Some [Inl 0] |)"

lemma "run rev [2, 3, 4] = Some [4, 3, 2]"
  by (simp add: run_def rev_def Update.comp_def hat_hom_def update2hom_def fold_sum_def idU_def)















