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
  states  :: "'q set"
  variables :: "'x set"
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

(* \<delta>\<^sup>^(q, w) *)
abbreviation delta_hat :: "('q, 'x, 'a, 'b, 'e) SST_scheme \<Rightarrow> ('q, 'a list) trans" where
  "delta_hat sst \<equiv> hat1 (delta sst)"

(* \<eta>(q, w) *)
abbreviation eta_hat :: "('q, 'x, 'a, 'b, 'e) SST_scheme \<Rightarrow> ('q, 'x, 'a list, 'b) updator" where
  "eta_hat sst \<equiv> hat2 (delta sst) (eta sst)"

(* extract only variables from var-alphabet list *)
fun extract_variables :: "('x + 'b) list \<Rightarrow> 'x list" where
  "extract_variables [] = []" |
  "extract_variables (Inl x#xs) = x # extract_variables xs" |
  "extract_variables (Inr a#xs) = extract_variables xs"


lemma [simp]: "extract_variables (u @ v) = extract_variables u @ extract_variables v"
  by (induct u arbitrary: v rule: xa_induct; simp_all)

lemma extract_variables_left_id[simp]: "extract_variables (map Inl u) = u"
  by (induct u, simp_all)

lemma extract_variables_right_ignore[simp]: "extract_variables (map Inr u) = []"
  by (induct u, simp_all)

(* remove variables in the output string *)
fun valuate :: "('x + 'b) list => 'b list" where
  "valuate []           = []" |
  "valuate (Inl x#rest) = valuate rest" |
  "valuate (Inr b#rest) = b # valuate rest"

lemma valuate_distrib[simp]: "valuate (as @ bs) == valuate as @ valuate bs"
  by (induction as rule: xa_induct, simp_all)

lemma valuate_map_Inr[simp]: "valuate (map Inr as) = as"
  by (induction as, simp_all)


subsection \<open>Well-definedness\<close>

definition closed_delta where
  "closed_delta sst \<equiv> \<forall>q\<in>SST.states sst. \<forall>a. SST.delta sst (q, a) \<in> SST.states sst"

definition closed_eta where
  "closed_eta sst \<equiv>
     \<forall>q\<in>SST.states sst. \<forall>a. \<forall>x\<in>SST.variables sst.
       \<forall>y\<in>set (extract_variables (SST.eta sst (q, a) x)).
         y \<in> SST.variables sst"

definition closed_final where
  "closed_final sst \<equiv>
    \<forall>q\<in>SST.states sst.
      \<forall>u\<in>set_option (SST.final sst q).
        \<forall>y\<in>set (extract_variables u). y \<in> SST.variables sst"

definition initial_in_states where
  "initial_in_states sst \<equiv> SST.initial sst \<in> SST.states sst"


definition well_defined where
  "well_defined sst \<equiv> closed_delta sst \<and> closed_eta sst \<and> closed_final sst \<and> initial_in_states sst"


(* if the output is undefined, return None, or return some output *)
definition run :: "('q, 'x, 'a, 'b) SST \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "run sst w = (case final sst (delta_hat sst (initial sst, w)) of
      Some u \<Rightarrow> Some ((valuate o (eta_hat sst (initial sst, w) \<bullet> (\<lambda>x. u))) (SOME x :: 'x. True)) |
      None   \<Rightarrow> None)"


subsection \<open>Lemmata\<close>

lemma delta_append: "hat1 t (q, (as @ bs)) = hat1 t (hat1 t (q, as), bs)"
  by (induction as arbitrary: q, auto)

lemma eta_append: "hat2 tf to (q, as @ bs) = hat2 tf to (q, as) \<bullet> hat2 tf to (hat1 tf (q, as), bs)"
  by (induction as arbitrary: q, auto simp add: comp_assoc comp_left_neutral)


lemma [simp]: "Transducer.hat1 d (q, w) = SST.hat1 d (q, w)"
  by (induction w arbitrary: q, auto)


subsection \<open>Examples\<close>

definition rev :: "(nat, nat, nat, nat) SST" where
  "rev = (|
    states = {0},
    variables = {0},
    initial = 0,
    delta = \<lambda>(q, a). 0,
    eta = \<lambda>(q, a) x. [Inr a, Inl 0],
    final = \<lambda>q. Some [Inl 0] |)"

lemmas well_definedness = 
  closed_delta_def closed_eta_def closed_final_def initial_in_states_def well_defined_def

lemma "well_defined rev"
  unfolding well_definedness rev_def
  by simp
  
definition reset :: "(nat, nat, nat, nat) SST" where
  "reset = \<lparr>
    states = {0},
    variables = {0},
    initial = 0,
    delta = \<lambda>(q, a). 0,
    eta = \<lambda>(q, a) x. (if a = 0 then [] else [Inl 0, Inr a]),
    final = \<lambda>q. Some [Inl 0] \<rparr>"

lemma "well_defined reset"
  unfolding reset_def well_definedness
  by simp

lemma "run reset [1, 2, 0, 1, 2] = Some [1, 2]"
  by (simp add: run_def reset_def Update.comp_def hat_hom_def update2hom_def fold_sum_def idU_def emptyU_def)


lemma "run rev [2, 3, 4] = Some [4, 3, 2]"
  by (simp add: run_def rev_def Update.comp_def hat_hom_def update2hom_def fold_sum_def idU_def emptyU_def)

end
