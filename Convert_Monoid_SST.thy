(* Title:   Convert_Monoid_SST.thy
   Author:  Akama Hitoshi
*)

section \<open>Convert a Monoid SST to a ordinary SST\<close>

theory Convert_Monoid_SST
  imports Main Update SST Monoid_SST Decompose_Update
begin

subsection \<open>Definition of another strange Transducer\<close>


definition \<iota>0 :: "('x \<Rightarrow> 'y shuffle) \<Rightarrow> 'x \<Rightarrow> ('y, 'x \<times> 'y index) update" where
  "\<iota>0 \<alpha> x = synthesize (\<alpha> x, (\<lambda>y'. [(x, y')]))"

definition \<iota> :: "('x \<Rightarrow> 'y shuffle) \<Rightarrow> ('x, ('y, 'x \<times> 'y index) update, 'b) update'" where
  "\<iota> \<alpha> x = [Inl (\<iota>0 \<alpha> x)]"

term "hat_hom (\<iota> alpha)"

fun coerce :: "(('y, 'x \<times> 'y index) update + ('y, 'b) update) \<Rightarrow> ('y, 'x \<times> 'y index + 'b) update" where
  "coerce (Inl mz) = (\<lambda>z. [Inl z]) \<star> mz" |
  "coerce (Inr mb) = (\<lambda>b. [Inr b]) \<star> mb"

definition \<tau> :: "(('y, 'x \<times> 'y index) update + ('y, 'b) update) list \<Rightarrow> ('y, 'x \<times> 'y index + 'b) update" where
  "\<tau> u = concatU (map coerce u)"

definition \<Delta>' :: "('x \<Rightarrow> 'y shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<Rightarrow> 'y shuffle)" where
  "\<Delta>' = (\<lambda>(\<alpha>, \<theta>). \<lambda>x. resolve_shuffle (\<tau> (hat_hom (\<iota> \<alpha>) (\<theta> x))))"

definition H' :: "('x \<Rightarrow> 'y shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<times> 'y index, 'b) update" where
  "H' = (\<lambda>(\<alpha>, \<theta>). \<lambda>(x, y'). resolve_store (\<tau> (hat_hom (\<iota> \<alpha>) (\<theta> x))) y')"


lemma \<Delta>'_assoc: "\<Delta>' (\<alpha>, \<phi> \<bullet> \<psi>) = \<Delta>' (\<Delta>' (\<alpha>, \<phi>), \<psi>)"
  sorry

lemma H'_assoc: "H' (\<alpha>, \<phi> \<bullet> \<psi>) = H' (\<alpha>, \<phi>) \<bullet> H' (\<Delta>' (\<alpha>, \<phi>), \<psi>)"
  sorry

lemma "\<Delta>' (\<alpha>, idU) = \<alpha>"
  apply (rule ext)
  apply (rule ext)
  apply (simp add: \<Delta>'_def \<tau>_def idU_def \<iota>_def resolve_shuffle_distrib resolve_idU_idS)
  apply (simp add: idS_def \<iota>0_def map_alpha_synthesize synthesize_def resolve_shuffle_distrib map_alpha_distrib)
  apply (simp add: map_alpha_synthesize_store map_alpha_synthesize_shuffle)
  oops

subsection \<open>Construction\<close>

definition convert_\<delta> :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow>
                         ('q \<times> ('x \<Rightarrow> 'y shuffle), 'a) trans" where
  "convert_\<delta> msst =
     (\<lambda>((q1, f), a). (MSST.delta msst (q1, a), \<Delta>' (f, MSST.eta msst (q1, a))))"

definition convert_\<eta> :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow>
                         ('q \<times> ('x \<Rightarrow> 'y shuffle), 'x \<times> 'y index, 'a, 'b) updator" where
  "convert_\<eta> msst = (\<lambda>((q, \<alpha>), b). H' (\<alpha>, MSST.eta msst (q, b)))"

definition convert_final :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow>
   ('q \<times> ('x \<Rightarrow> 'y shuffle) \<Rightarrow> ('x \<times> 'y index + 'b) list option)" where
  "convert_final msst = (\<lambda>(q, \<alpha>).
     (case MSST.final_update msst q of
        Some u \<Rightarrow> (case MSST.final_string msst q of
          Some v \<Rightarrow> Some (valuate (hat_hom (\<tau> (hat_hom (\<iota> \<alpha>) u)) (hat_alpha (\<lambda>b. [Inr b]) v))) |
          None \<Rightarrow> None) |
        None \<Rightarrow> None))"

lemma convert_\<delta>_simp: "convert_\<delta> msst ((q1, f), a) = (MSST.delta msst (q1, a), \<Delta>' (f, MSST.eta msst (q1, a)))"
  by (simp add: convert_\<delta>_def)

lemma convert_\<eta>_simp: "convert_\<eta> msst ((q1, f), a) = H' (f, MSST.eta msst (q1, a))"
  by (simp add: convert_\<eta>_def)

definition convert_MSST :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow>
                            ('q \<times> ('x \<Rightarrow> 'y shuffle), 'x \<times> 'y index, 'a, 'b) SST" where
  "convert_MSST msst = \<lparr>
    SST.initial = (MSST.initial msst, \<lambda>x. idS),
    delta       = convert_\<delta> msst,
    eta         = convert_\<eta> msst,
    final       = convert_final msst
  \<rparr>"


subsection \<open>Properties\<close>

lemma convert_\<delta>_hat:
  "SST.hat1 (convert_\<delta> msst) ((q, \<alpha>), w) =
   (Monoid_SST.delta_hat msst (q, w), \<Delta>' (\<alpha>, Monoid_SST.eta_hat msst (q, w)))"
proof (induct w arbitrary: q \<alpha>)
  case Nil
  then show ?case apply (simp add: convert_\<delta>_def)
    apply (rule ext)
    apply (simp add: \<Delta>'_def \<tau>_def idU_def)
    sorry
next
  case (Cons a w)
  then show ?case by (simp add: \<Delta>'_assoc convert_\<delta>_def)
qed
  

lemma convert_\<eta>_hat:
  "SST.hat2 (convert_\<delta> msst) (convert_\<eta> msst) ((q, \<alpha>), w) =
   H' (\<alpha>, Monoid_SST.eta_hat msst (q, w))"
proof (induct w arbitrary: q \<alpha>)
  case Nil
  then show ?case apply (simp add: convert_\<delta>_def)
    apply (rule ext)
    apply (simp add: \<Delta>'_def \<tau>_def idU_def)
    sorry
next
  case (Cons a w)
  then show ?case by (simp add: convert_\<delta>_simp convert_\<eta>_simp H'_assoc)
qed
  




end



