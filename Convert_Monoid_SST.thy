(* Title:   Convert_Monoid_SST.thy
   Author:  Akama Hitoshi
*)

section \<open>Convert a Monoid SST to a ordinary SST\<close>

theory Convert_Monoid_SST
  imports Main Update SST Monoid_SST Decompose_update
begin

subsection \<open>Definition of another strange Transducer\<close>


definition \<iota>0 :: "('x \<Rightarrow> 'y shuffle) \<Rightarrow> 'x \<Rightarrow> ('y, 'x \<times> 'y location) update" where
  "\<iota>0 \<alpha> x = synthesize (\<alpha> x, (\<lambda>y'. [(x, Inl y')]), (\<lambda>y. [(x, Inr y)]))"

definition \<iota> :: "('x \<Rightarrow> 'y shuffle) \<Rightarrow> ('x, ('y, 'x \<times> 'y location) update, 'b) update'" where
  "\<iota> \<alpha> x = [Inl (\<iota>0 \<alpha> x)]"

term "hat_hom (\<iota> alpha)"

fun coerce :: "(('y, 'x \<times> 'y location) update + ('y, 'b) update) \<Rightarrow> ('y, 'x \<times> 'y location + 'b) update" where
  "coerce (Inl mz) = (\<lambda>z. [Inl z]) \<star> mz" |
  "coerce (Inr mb) = (\<lambda>b. [Inr b]) \<star> mb"

definition \<tau> :: "(('y, 'x \<times> 'y location) update + ('y, 'b) update) list \<Rightarrow> ('y, 'x \<times> 'y location + 'b) update" where
  "\<tau> u = concatU (map coerce u)"

definition \<Delta>' :: "('x \<Rightarrow> 'y shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<Rightarrow> 'y shuffle)" where
  "\<Delta>' = (\<lambda>(\<alpha>, \<theta>). \<lambda>x. resolve_shuffle (\<tau> (hat_hom (\<iota> \<alpha>) (\<theta> x))))"

definition H' :: "('x \<Rightarrow> 'y shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<times> 'y location, 'b) update" where
  "H' = (\<lambda>(\<alpha>, \<theta>). \<lambda>(x, y'). lookup_store (resolve_store (\<tau> (hat_hom (\<iota> \<alpha>) (\<theta> x)))) y')"


lemma \<Delta>'_assoc: "\<Delta>' (\<alpha>, \<phi> \<bullet> \<psi>) = \<Delta>' (\<Delta>' (\<alpha>, \<phi>), \<psi>)"
  sorry

lemma H'_assoc: "H' (\<alpha>, \<phi> \<bullet> \<psi>) = H' (\<alpha>, \<phi>) \<bullet> H (\<Delta>' (\<alpha>, \<phi>), \<psi>)"
  sorry


subsection \<open>Construction\<close>

definition convert_\<delta> :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow>
                         ('q \<times> ('x \<Rightarrow> 'y shuffle), 'a) trans" where
  "convert_\<delta> msst =
     (\<lambda>((q1, f), a). (MSST.delta msst (q1, a), \<Delta>' (f, MSST.eta msst (q1, a))))"

definition convert_\<eta> :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow>
                         ('q \<times> ('x \<Rightarrow> 'y shuffle), 'x \<times> 'y location, 'a, 'b) updator" where
  "convert_\<eta> msst = (\<lambda>((q, \<alpha>), b). H' (\<alpha>, MSST.eta msst (q, b)))"

definition convert_final :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow>
   ('q \<times> ('x \<Rightarrow> 'y shuffle) \<Rightarrow> ('x \<times> 'y location + 'b) list option)" where
  "convert_final msst = (\<lambda>(q, \<alpha>).
     (case MSST.final_update msst q of
        Some u \<Rightarrow> (case MSST.final_string msst q of
          Some v \<Rightarrow> Some (valuate (hat_hom (\<tau> (hat_hom (\<iota> \<alpha>) u)) (hat_alpha (\<lambda>b. [Inr b]) v))) |
          None \<Rightarrow> None) |
        None \<Rightarrow> None))"


definition convert_MSST :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow>
                            ('q \<times> ('x \<Rightarrow> 'y shuffle), 'x \<times> 'y location, 'a, 'b) SST" where
  "convert_MSST msst = \<lparr>
    SST.initial = (MSST.initial msst, \<lambda>x. idS),
    delta       = convert_\<delta> msst,
    eta         = convert_\<eta> msst,
    final       = convert_final msst
  \<rparr>"


end



