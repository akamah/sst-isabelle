(* Title:   Convert_Monoid_SST.thy
   Author:  Akama Hitoshi
*)

section \<open>Convert a Monoid SST to a ordinary SST\<close>

theory Convert_Monoid_SST
  imports Main Update SST Monoid_SST Decompose_Update
begin

subsection \<open>Definition of another strange Transducer\<close>


definition \<iota> :: "('x \<Rightarrow> 'y shuffle) \<Rightarrow> ('x, ('y, 'x \<times> 'y index) update, 'b) update'" where
  "\<iota> \<alpha> x = [Inl (synthesize (\<alpha> x, (\<lambda>y'. [(x, y')])))]"

term "hat_hom (\<iota> alpha)"

fun coerce :: "(('y, 'x \<times> 'y index) update + ('y, 'b) update) \<Rightarrow> ('y, 'x \<times> 'y index + 'b) update" where
  "coerce (Inl mz) = (\<lambda>z. [Inl z]) \<star> mz" |
  "coerce (Inr mb) = (\<lambda>b. [Inr b]) \<star> mb"

definition \<tau> :: "(('y, 'x \<times> 'y index) update + ('y, 'b) update) list \<Rightarrow> ('y, 'x \<times> 'y index + 'b) update" where
  "\<tau> u = concatU (map coerce u)"

definition \<Delta>' :: "('x \<Rightarrow> 'y shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<Rightarrow> 'y shuffle)" where
  "\<Delta>' = (\<lambda>(\<alpha>, \<theta>). \<lambda>x. resolve_shuffle (\<tau> (hat_hom (\<iota> \<alpha>) (\<theta> x))))"

definition H' :: "('x \<Rightarrow> 'y shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<times> 'y index, 'b) update" where
  "H' = (\<lambda>(\<alpha>, \<theta>). \<lambda>(x, y'). resolve_store (\<lambda>(y1, k1). [Inl (x, y1, k1)]) (\<tau> (hat_hom (\<iota> \<alpha>) (\<theta> x))) y')"

lemma \<tau>_nil: "\<tau> [] = idU" by (simp add: \<tau>_def)

lemma \<tau>_simp_alpha: "\<tau> (Inr m # u) = (\<lambda>b. [Inr b]) \<star> m \<bullet> \<tau> u"
  by (simp add: \<tau>_def)

lemma \<tau>_simp_var: "\<tau> (Inl mz # u) = (\<lambda>z. [Inl z]) \<star> mz \<bullet> \<tau> u"
  by (simp add: \<tau>_def)

lemma \<tau>_distrib[simp]: "\<tau> (u @ v) = \<tau> u \<bullet> \<tau> v"
  unfolding \<tau>_def
  by (simp add: concatU_append)

lemma \<Delta>'_assoc_string:
  fixes \<alpha> :: "'x \<Rightarrow> 'y shuffle"
  fixes \<theta> :: "('x, ('y, 'b) update) update"
  fixes u :: "('x + ('y, 'b) update) list"
  fixes y :: "'y"
  shows "resolve_shuffle (\<tau> (hat_hom (\<iota> \<alpha>) (hat_hom \<theta> u))) y
 = resolve_shuffle (\<tau> (hat_hom (\<iota> (\<lambda>y. resolve_shuffle (\<tau> (hat_hom (\<iota> \<alpha>) (\<theta> y))))) u)) y"
proof (induct u rule: xa_induct)
  case Nil
  then show ?case by (simp add: \<tau>_def resolve_shuffle_def idU_def)
next
  case (Var x xs)
  then show ?case
    apply (simp add: resolve_shuffle_distrib)
    apply (simp add: \<iota>_def map_alpha_synthesize synthesize_inverse_shuffle \<tau>_simp_var \<tau>_nil comp_right_neutral)
    done
next
  case (Alpha a xs)
  then show ?case by (simp add: \<tau>_simp_alpha resolve_shuffle_distrib)
qed


lemma \<Delta>'_assoc: "\<Delta>' (\<alpha>, \<phi> \<bullet> \<psi>) = \<Delta>' (\<Delta>' (\<alpha>, \<phi>), \<psi>)"
  by (intro ext, simp add: \<Delta>'_def comp_def \<Delta>'_assoc_string)

lemma H'_assoc: "H' (\<alpha>, \<phi> \<bullet> \<psi>) = H' (\<alpha>, \<phi>) \<bullet> H' (\<Delta>' (\<alpha>, \<phi>), \<psi>)"
  sorry


definition myconst where
  "myconst x y = x"

definition myid where
  "myid x = x"


subsection \<open>Construction\<close>

definition \<alpha>0 :: "'x \<Rightarrow> 'y shuffle" where
  "\<alpha>0 x = idS"


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
    SST.initial = (MSST.initial msst, \<alpha>0),
    delta       = convert_\<delta> msst,
    eta         = convert_\<eta> msst,
    final       = convert_final msst
  \<rparr>"


subsection \<open>Properties\<close>

lemma convert_\<delta>_hat:
  "SST.hat1 (convert_\<delta> msst) ((q, \<alpha>0), w) =
   (Monoid_SST.delta_hat msst (q, w), \<Delta>' (\<alpha>0, Monoid_SST.eta_hat msst (q, w)))"
proof (induct w arbitrary: q rule: rev_induct)
  case Nil
  then show ?case 
    apply (simp add: convert_\<delta>_def)
    apply (rule ext, rule ext)
    apply (simp add: \<Delta>'_def \<tau>_def idU_def \<iota>_def comp_right_neutral map_alpha_synthesize \<alpha>0_def idS_def)
    apply (simp add: resolve_shuffle_def synthesize_def synthesize_shuffle_def comp_def)
    apply (simp add: scan_def padding_def synthesize_store_def)
    done
next
  case (snoc a w)
  then show ?case by (simp add: delta_append eta_append comp_right_neutral  \<Delta>'_assoc convert_\<delta>_def)
qed


lemma convert_\<eta>_hat:
  "SST.hat2 (convert_\<delta> msst) (convert_\<eta> msst) ((q0, \<alpha>0), w) =
   H' (\<alpha>0, Monoid_SST.eta_hat msst (q0, w))"
proof (induct w rule: rev_induct)
  case Nil
  then show ?case proof (rule ext)
    fix xyk
    show "SST.hat2 (convert_\<delta> msst) (convert_\<eta> msst) ((q0, \<alpha>0), []) xyk = H' (\<alpha>0, Monoid_SST.eta_hat msst (q0, [])) xyk"
    proof (cases xyk)
      case (fields x y k)
      then show ?thesis proof (cases k)
        case 0
        then show ?thesis
          apply (simp add: convert_\<delta>_def fields)
          apply (simp add: \<Delta>'_def \<tau>_def idU_def \<alpha>0_def idS_def H'_def)
          apply (simp add: \<iota>_def comp_right_neutral map_alpha_synthesize)
          unfolding resolve_store_def scan_def synthesize_def 
            synthesize_shuffle_def padding_def synthesize_store_def comp_def
          apply (simp add: \<alpha>0_def idS_def)
          done
        next
          case (Suc nat)
          then show ?thesis
            apply (simp add: convert_\<delta>_def fields)
            apply (simp add: \<Delta>'_def \<tau>_def idU_def \<alpha>0_def idS_def H'_def)
            apply (simp add: \<iota>_def comp_right_neutral map_alpha_synthesize)
            unfolding resolve_store_def scan_def synthesize_def 
              synthesize_shuffle_def padding_def synthesize_store_def comp_def
            apply (simp add: \<alpha>0_def idS_def)
            sorry
        qed
      qed
    qed
next
  case (snoc a w)
  then show ?case
    by (simp add: delta_append eta_append comp_right_neutral H'_assoc convert_\<eta>_def convert_\<delta>_hat)
qed


theorem MSST_can_convert:
  "SST.run (convert_MSST msst) w = Monoid_SST.run msst w"
proof (cases "MSST.final_update msst (hat1 (delta msst) (initial msst, w))")
  case None
  then show ?thesis
    by (simp add: convert_MSST_def SST.run_def Monoid_SST.run_def convert_final_def convert_\<delta>_hat)
next
  case Some1: (Some m)
  then show ?thesis proof (cases "MSST.final_string msst (hat1 (delta msst) (initial msst, w))")
    case None
    then show ?thesis
      by (simp add: convert_MSST_def SST.run_def Monoid_SST.run_def convert_final_def convert_\<delta>_hat Some1)
  next
    case Some2: (Some u)
    then show ?thesis
      apply (simp add: convert_MSST_def SST.run_def Monoid_SST.run_def convert_final_def convert_\<delta>_hat convert_\<eta>_hat Some1)
      
  qed
qed

end



