(* Title:   Compose.thy
   Author:  Akama Hitoshi
*)

section \<open>Composition of two SSTs\<close>

theory Compose
  imports Main Compose_SST_SST Convert_Monoid_SST
          "../Type/Compose_SST_SST_Type" "../Bounded_Copy/Bounded_Copy_SST_SST" "../Type/Compose_SST_SST_Type" "../Bounded_Copy/Bounded_Copy_Convert"
    "HOL-Library.Cardinality"
begin

(* This is type of the state of composed SST.
 * bc_shuffle means M_{x2, \<emptyset>} which is e2-bounded-copy.
 * e2 is type-level natural number
 *)
type_synonym ('e2, 'q1, 'q2, 'x1, 'x2) composed_state = "('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2)) \<times> ('q2 \<times> 'x1 \<Rightarrow> ('e2, 'x2) bc_shuffle)" 

(* This is type of the variable of compose SST.
 * `e2 'option` is type level natural number means `e2 + 1`
 *)
type_synonym ('e2, 'q2, 'x1, 'x2) composed_var = "('q2 \<times> 'x1) \<times> ('x2 \<times> 'e2 option)"


abbreviation compose ::
  "'e2::enum boundedness
\<Rightarrow> ('q1::enum, 'x1::enum, 'a, 'b) SST
\<Rightarrow> ('q2::enum, 'x2::enum, 'b, 'c) SST
\<Rightarrow> (('e2, 'q1, 'q2, 'x1, 'x2) composed_state, ('e2, 'q2, 'x1, 'x2) composed_var, 'a, 'c) SST" where
  "compose B sst1 sst2 \<equiv> convert_MSST B (compose_SST_SST sst1 sst2)"


theorem SST_can_compose:
  assumes "boundedness B k"
  assumes "bounded_copy_SST k sst2"
  assumes "trim sst2" (* without loss of generality, we can assume sst2 is trim *)
  shows "SST.run (compose B sst1 sst2) w = Option.bind (SST.run sst1 w) (SST.run sst2)"
proof -
  let ?gm = "compose_\<gamma> sst1 sst2"
  let ?comp = "compose_SST_SST sst1 sst2"
  have "bctype k ?comp ?gm" by (simp add: compose_typable assms)
  then show ?thesis unfolding compose_def using assms
    by (simp add: MSST_can_convert can_compose_SST_SST)
qed

theorem composed_SST_bounded:
  fixes sst1 :: "('q1::enum, 'x1::enum, 'a, 'b) SST"
  fixes sst2 :: "('q2::enum, 'x2::enum, 'b, 'c) SST"
  fixes B1 :: "'e1::enum boundedness"
  fixes B2 :: "'e2::enum boundedness"
  assumes "boundedness B1 k"
  assumes "boundedness B2 l"
  assumes "bounded_copy_SST k sst1"
  assumes "bounded_copy_SST l sst2"
  assumes "trim sst2"
  shows "bounded_copy_SST (card (UNIV::'q2 set) * k * l) (compose B2 sst1 sst2)"
proof -
  let ?msst = "compose_SST_SST sst1 sst2"
  let ?gamma = "compose_\<gamma> sst1 sst2"
  let ?Bq2_k = "Boundedness :: ('q2 \<times> 'e1) boundedness"
  let ?q2_k = "card (UNIV::'q2 set) * k"
  have bound: "boundedness ?Bq2_k ?q2_k"
    using assms(1)
    unfolding boundedness_def by (simp add: card_UNIV_length_enum[symmetric] UNIV_Times_UNIV[symmetric] del: UNIV_Times_UNIV)
  have bc_msst: "bounded_copy_SST ?q2_k ?msst"
    by (simp add: compose_SST_SST_bounded assms(3))
  have bc_type: "bctype l ?msst ?gamma"
    by (simp add: compose_typable assms(4-5))
  show ?thesis
    by (rule convert_MSST_bounded[OF bc_msst bound assms(2) bc_type])
qed


theorem composed_SST_state:
  fixes sst1 :: "('q1::enum, 'x1::enum, 'a, 'b) SST"
  fixes sst2 :: "('q2::enum, 'x2::enum, 'b, 'c) SST"
  fixes B2 :: "'e2::enum boundedness"
  shows "CARD(('e2, 'q1, 'q2, 'x1, 'x2) composed_state)
      = CARD('q1) * CARD('q2) ^ (CARD('q2) * CARD('x1)) 
      * CARD(('e2, 'x2) bc_shuffle) ^ (CARD('q2) * CARD('x1))"
  by (simp del: UNIV_Times_UNIV add: finite_UNIV_card_ge_0 card_fun)

theorem composed_SST_var:
  fixes sst1 :: "('q1::enum, 'x1::enum, 'a, 'b) SST"
  fixes sst2 :: "('q2::enum, 'x2::enum, 'b, 'c) SST"
  fixes B2 :: "'e2::enum boundedness"
  shows "CARD(('e2, 'q2, 'x1, 'x2) composed_var)
      = CARD('q2) * CARD('x1) * CARD('x2) * (CARD('e2) + 1)"
  by (simp add: distrib_left)


subsection \<open>Examples\<close>

definition revrev where
  "revrev = compose_SST_SST rev rev"

definition revreset where
  "revreset = compose_SST_SST rev reset"

value "SST.run rev [1, 2, 3]"


definition rev :: "(Enum.finite_1, Enum.finite_1, Enum.finite_2, Enum.finite_2) SST" where
  "rev = (|
    initial = 0,
    delta = \<lambda>(q, a). 0,
    eta = \<lambda>(q, a) x. [Inr a, Inl 0],
    final = \<lambda>q. Some [Inl 0] |)"

definition revhoge :: "(Enum.finite_2, Enum.finite_2, Enum.finite_2, Enum.finite_2) SST" where
  "revhoge = (|
    initial = 0,
    delta = \<lambda>(q, a). a,
    eta = \<lambda>(q, a) x. (if x = 0 then [Inl 0, Inr a] else [Inr a, Inl 1]),
    final = \<lambda>q. (if q = 0 then Some [Inl 0] else Some [Inl 1]) |)"

definition
  "revrevhoge = compose_SST_SST rev revhoge"

definition
  "revhogebound = (Boundedness :: Enum.finite_1 boundedness)"

definition
  "revrevhogeconv = convert_MSST revhogebound revrevhoge"





end
