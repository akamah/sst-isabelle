(* Title:   SST.thy
   Author:  Akama Hitoshi
*)

section \<open>The definition of streaming string transducers\<close>

theory SST
  imports Main Update State_Machine Transducer
begin

(* type of variable update function *)
type_synonym ('q, 'x, 'a, 'b) "updator" =
  "'q \<times> 'a \<Rightarrow> ('x, 'b) update"

record ('q, 'x, 'a, 'b) SST = "('q, 'a) state_machine" + 
  variables :: "'x set"
  eta     :: "('q, 'x, 'a, 'b) updator"
  final   :: "'q \<Rightarrow> ('x + 'b) list option"

(* string input version of variable update function *)
fun hat2 :: "('q, 'a) trans \<Rightarrow> ('q, 'x, 'a, 'b) updator \<Rightarrow> ('q, 'x, 'a list, 'b) updator" where
  "hat2 t u (q, [])     = idU" |
  "hat2 t u (q, (a#as)) = u (q, a) \<bullet> hat2 t u (t (q, a), as)"

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

definition closed_eta where
  "closed_eta sst \<equiv>
     \<forall>q\<in>states sst. \<forall>a. \<forall>x\<in>SST.variables sst.
       SST.eta sst (q, a) x \<in> star (SST.variables sst <+> UNIV)"

definition closed_final where
  "closed_final sst \<equiv>
    \<forall>q\<in>states sst.
      \<forall>u\<in>set_option (SST.final sst q). u \<in> star (SST.variables sst <+> UNIV)"

abbreviation well_defined where
  "well_defined sst \<equiv> st_well_defined sst \<and> closed_eta sst \<and> closed_final sst"

lemmas well_defined_simps = st_well_defined_simps closed_eta_def closed_final_def


(* if the output is undefined, return None, or return some output *)
definition run :: "('q, 'x, 'a, 'b, 'e) SST_scheme \<Rightarrow> 'a list \<Rightarrow> 'b list option" where
  "run sst w = (case final sst (delta_hat sst (initial sst, w)) of
      Some u \<Rightarrow> Some ((valuate o (eta_hat sst (initial sst, w) \<bullet> (\<lambda>x. u))) (SOME x :: 'x. True)) |
      None   \<Rightarrow> None)"


subsection \<open>Lemmata\<close>

lemma eta_append: "hat2 tf to (q, as @ bs) = hat2 tf to (q, as) \<bullet> hat2 tf to (hat1 tf (q, as), bs)"
  by (induction as arbitrary: q, auto simp add: comp_assoc comp_left_neutral)


lemma extract_star:
  assumes "\<forall>y\<in>set (extract_variables u). y\<in>V"
  shows "u \<in> star (V <+> UNIV)"
using assms by (induct u rule: xa_induct, auto simp add: star_def)


(*
lemma eta_closed_iff: 
  assumes "closed_eta sst"
  assumes "q1 \<in> states sst"
  assumes "x1 \<in> variables sst"
  shows "SST.eta sst (q1, a) x1 \<in> star (variables sst <+> UNIV)"
  apply (rule extract_star)
  using assms
  unfolding well_defined_simps
  by auto
*)
  
  

subsection \<open>Examples\<close>

definition rev :: "(nat, nat, nat, nat) SST" where
  "rev = (|
    states = {0},
    initial = 0,
    delta = \<lambda>(q, a). 0,
    variables = {0},
    eta = \<lambda>(q, a) x. [Inr a, Inl 0],
    final = \<lambda>q. Some [Inl 0] |)"

lemma "well_defined rev"
  unfolding well_defined_simps rev_def star_def
  by auto
  
definition reset :: "(nat, nat, nat, nat) SST" where
  "reset = \<lparr>
    states = {0},
    initial = 0,
    delta = \<lambda>(q, a). 0,
    variables = {0},
    eta = \<lambda>(q, a) x. (if a = 0 then [] else [Inl 0, Inr a]),
    final = \<lambda>q. Some [Inl 0] \<rparr>"

lemma "well_defined reset"
  unfolding reset_def well_defined_simps star_def
  by auto

lemma "run reset [1, 2, 0, 1, 2] = Some [1, 2]"
  by (simp add: run_def reset_def Update.comp_def hat_hom_def update2hom_def fold_sum_def idU_def emptyU_def)


lemma "run rev [2, 3, 4] = Some [4, 3, 2]"
  by (simp add: run_def rev_def Update.comp_def hat_hom_def update2hom_def fold_sum_def idU_def emptyU_def)

end
