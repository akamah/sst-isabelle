(* Title:   Convert_Monoid_SST.thy
   Author:  Akama Hitoshi
*)

section \<open>Convert a Monoid SST to a ordinary SST\<close>

theory Convert_Monoid_SST
  imports Main Update SST Monoid_SST Decompose_Update Sum_Type
begin

subsection \<open>Definition of another strange Transducer\<close>

definition update2homU ::
  "('x \<Rightarrow> ('y, 'z + 'b) update) \<Rightarrow> 
   ('x + ('y, 'b) update) \<Rightarrow>
   ('y, 'z + 'b) update"where
  "update2homU \<phi> = fold_sum \<phi> (op \<star> inr_list)"

definition hat_homU ::
  "('x \<Rightarrow> ('y, 'z + 'b) update) \<Rightarrow> 
   ('x + ('y, 'b) update) list \<Rightarrow>
   ('y, 'z + 'b) update" where
  "hat_homU \<phi> = concatU o map (update2homU \<phi>)"

lemma [simp]: "hat_homU \<phi> [] = idU"
  by (simp add: hat_homU_def)

lemma [simp]: "hat_homU \<phi> (Inl x # u) = \<phi> x \<bullet> hat_homU \<phi> u"
  by (simp add: hat_homU_def update2homU_def)

lemma [simp]: "hat_homU \<phi> (Inr m # u) = inr_list \<star> m \<bullet> hat_homU \<phi> u"
  by (simp add: hat_homU_def update2homU_def)

lemma hat_homU_append: "hat_homU \<phi> (u @ v) = hat_homU \<phi> u \<bullet> hat_homU \<phi> v"
  by (simp add: hat_homU_def concatU_append)



fun embed :: "'x \<Rightarrow> 'y \<Rightarrow> ('x \<times> 'y + 'b) list" where
  "embed x y = [Inl (x, y)]"

definition \<iota> :: "('x \<Rightarrow> 'y shuffle) \<Rightarrow> 'x \<Rightarrow> ('y, 'x \<times> 'y index + 'b) update" where
  "\<iota> \<alpha> x = synthesize (\<alpha> x, embed x)"


definition \<Delta>' :: "('x \<Rightarrow> 'y shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<Rightarrow> 'y shuffle)" where
  "\<Delta>' = (\<lambda>(\<alpha>, \<theta>). \<lambda>x. resolve_shuffle (hat_homU (\<iota> \<alpha>) (\<theta> x)))"

fun default_string where
  "default_string x = embed x"

definition H' :: "('x \<Rightarrow> 'y shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<times> 'y index, 'b) update" where
  "H' = (\<lambda>(\<alpha>, \<theta>). \<lambda>(x, y'). resolve_store (default_string x) (hat_homU (\<iota> \<alpha>) (\<theta> x)) y')"


lemma \<Delta>'_assoc_string:
  fixes \<alpha> :: "'x \<Rightarrow> 'y shuffle"
  fixes \<theta> :: "('x, ('y, 'b) update) update"
  fixes u :: "('x + ('y, 'b) update) list"
  fixes y :: "'y"
  shows "resolve_shuffle (hat_homU (\<iota> \<alpha>) (hat_hom \<theta> u)) y
 = resolve_shuffle (hat_homU (\<iota> (\<lambda>y. resolve_shuffle (hat_homU (\<iota> \<alpha>) (\<theta> y)))) u) y"
proof (induct u rule: xa_induct)
  case Nil
  then show ?case by (simp add: resolve_shuffle_def idU_def)
next
  case (Var x xs)
  then show ?case
    apply (simp add: resolve_shuffle_distrib)
    apply (simp add: hat_homU_append resolve_shuffle_distrib)
    apply (simp add: \<iota>_def synthesize_inverse_shuffle)
    done
next
  case (Alpha a xs)
  then show ?case by (simp add: resolve_shuffle_distrib)
qed


lemma \<Delta>'_assoc: "\<Delta>' (\<alpha>, \<phi> \<bullet> \<psi>) = \<Delta>' (\<Delta>' (\<alpha>, \<phi>), \<psi>)"
  by (intro ext, simp add: \<Delta>'_def comp_def \<Delta>'_assoc_string)


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
          Some v \<Rightarrow> Some (valuate (hat_hom (hat_homU (\<iota> \<alpha>) u) (hat_alpha inr_list v))) |
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



lemma hat_hom_valuate:
  fixes t :: "('y, 'z, 'b) update'"
  fixes \<theta> :: "('w, 'x, 'y + 'b) update'"
  shows "hat_hom t (valuate (\<theta> x)) = valuate ((update2hom t \<star> \<theta>) x)"
proof -
  { fix u :: "('x + 'y + 'b) list"
    have "hat_hom t (valuate u) = valuate (hat_alpha (update2hom t) u)"
      by (induct u rule: xa_induct, simp_all add: hat_hom_def)
  }
  then show ?thesis by (simp add: map_alpha_def)
qed


(* TODO: this lemma is a combination of hat_hom_valuate
 * and distribute law of star operator 
 *)
lemma hat_hom_valuate_hat_hom:
  fixes t :: "('z, 'z, 'b) update'"
  fixes \<phi> :: "('w, 'x, 'z + 'b) update'"
  shows "hat_hom t (valuate (hat_hom \<phi> u)) = valuate (hat_hom (update2hom t \<star> \<phi>) (hat_alpha (update2hom t) u))"
proof (induct u rule: xa_induct)
case Nil
  then show ?case by (simp add: map_alpha_def)
  case (Var x xs)
  then show ?case by (simp add: hat_hom_valuate map_alpha_def)
next
  case (Alpha a xs)
  then show ?case proof (cases a)
    case (Inl z)
    then show ?thesis by (simp add: map_alpha_def Alpha hat_hom_right_ignore)
  next
    case (Inr b)
    then show ?thesis by (simp add: map_alpha_def Alpha)
  qed
qed

lemma hat_hom_valuate_fun:
  shows "t \<bullet> (valuate o \<theta>) = valuate o (update2hom t \<star> \<theta>)"
  by (rule ext, simp add: comp_def hat_hom_valuate)

lemma valuate_hat_hom_emptyU: "valuate (hat_hom emptyU w) = valuate w"
  by (induct w rule: xa_induct, simp_all add: emptyU_def)


lemma update2hom_hat_alpha: "hat_alpha (update2hom t) (hat_alpha inr_list w) = hat_alpha inr_list w"
  by (induct w rule: xa_induct, simp_all)

lemma update2hom_inr_list: "update2hom t \<star> (inr_list \<star> m) = inr_list \<star> m"
  by (auto simp add: map_alpha_def update2hom_hat_alpha)


lemma hat_homU_map_alpha:
  "update2hom t \<star> hat_homU \<phi> m = hat_homU (map_alpha (update2hom t) o \<phi>) m"
proof (induct m)
  case Nil
  then show ?case by (simp add: map_alpha_def idU_def)
next
  case (Cons a m)
  then show ?case proof (cases a)
    case (Inl z)
    then show ?thesis by (simp add: map_alpha_distrib Cons)
  next
    case (Inr b)
    then show ?thesis by (simp add: map_alpha_distrib Cons update2hom_inr_list)
  qed
qed  



lemma H'_embed: "H' (\<alpha>, \<theta>) \<bullet> embed x = resolve_store (default_string x) (hat_homU (\<iota> \<alpha>) (\<theta> x))"
  by (auto simp add: comp_def H'_def)


lemma map_alpha_H'_iota_\<Delta>:
  fixes x :: "'x"
  fixes \<alpha> :: "'x \<Rightarrow> 'y shuffle"
  fixes \<theta> :: "('x, ('y, 'b) update) update"
  shows "map_alpha (update2hom (H' (\<alpha>, \<theta>))) o \<iota> (\<Delta>' (\<alpha>, \<theta>)) = hat_homU (\<iota> \<alpha>) o \<theta>"
  apply (rule ext)
  apply (simp add: \<iota>_def)
  apply (simp add: map_alpha_synthesize comp_def[symmetric] hat_hom_def[symmetric])
  apply (simp add: H'_embed \<Delta>'_def)
  apply (simp add: resolve_inverse)
  done


fun ignore_left where
  "ignore_left (Inl x) = []" |
  "ignore_left (Inr a) = [a]"

lemma valuate_ignore_left: "valuate = concat o map ignore_left"
proof -
  have 1: "\<And>xs. valuate xs = concat (map ignore_left xs)"
    by (induct_tac xs rule: xa_induct, auto)
  show ?thesis by (rule ext, auto simp add: 1)
qed

lemma valuate_update: "valuate (valuate u) = valuate (hat_alpha ignore_left u)"
proof (induct u rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case by simp
next
  case (Alpha a xs)
  then show ?case by (cases a, simp_all)
qed

lemma valuate_update_map_alpha: "valuate (valuate (\<theta> x)) = valuate ((ignore_left \<star> \<theta>) x)"
  by (simp add: map_alpha_def valuate_update)

lemma synthesize_idU: "synthesize (idS :: 'x \<Rightarrow> 'x list, \<lambda>(y, k). []) = (idU :: ('x, 'a) update)"
proof -
  have 1: "(idS :: 'x \<Rightarrow> 'x list) = resolve_shuffle (idU :: ('x, 'a) update)"
    by (simp add: resolve_idU_idS[symmetric])
  have 2: "(\<lambda>(y, k). []) = resolve_store (\<lambda>x. []) idU"
    by (auto simp add: resolve_idU_empty)
  show ?thesis by (simp add: 1 2 resolve_inverse)
qed


definition idA :: "'x \<Rightarrow> 'x list" where
  "idA x = [x]"

lemma ignore_left_inr_list_eq_idA: "(concat o map ignore_left o inr_list) = idA" unfolding idA_def by auto
lemma map_alpha_idA: "idA \<star> m = m"
proof -
  have 1: "\<And>w. hat_alpha idA w = w" by (induct_tac w rule: xa_induct, simp_all add: idA_def)
  show ?thesis by (rule ext, auto simp add: map_alpha_def 1)
qed

lemma ignore_left_inr_list: "ignore_left \<star> (inr_list \<star> a) = a"
  by (auto simp add: map_alpha_assoc ignore_left_inr_list_eq_idA map_alpha_idA)

lemma ignore_left_iota_alpha0: "ignore_left \<star> \<iota> \<alpha>0 x = idU"
proof -
  have 1: "concat o map ignore_left o embed x= (\<lambda>(y, k). [])"
    by auto
  show ?thesis 
    by (simp add: \<iota>_def synthesize_store_def map_alpha_synthesize \<alpha>0_def 1 synthesize_idU)
qed

lemma ignore_left_hat_hom_iota_alpha0:
  "ignore_left \<star> hat_homU (\<iota> \<alpha>0) u = concatU (valuate u)"
proof (induct u rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case by (simp add: ignore_left_iota_alpha0 map_alpha_distrib comp_left_neutral)
next
  case (Alpha m xs)
  then show ?case by (simp add: map_alpha_distrib ignore_left_inr_list) 
qed



lemma ignore_left_hat_homU_iota_alpha0: "ignore_left \<star> hat_homU (\<iota> \<alpha>0) m = concatU (valuate m)"
proof (induct m rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case by (simp add: map_alpha_distrib ignore_left_iota_alpha0 comp_left_neutral)
next
  case (Alpha a xs)
  then show ?case by (simp add: map_alpha_distrib ignore_left_inr_list)
qed


lemma hat_homU_lem: "hat_homU (hat_homU \<phi> o \<theta>) m = hat_homU \<phi> (hat_hom \<theta> m)"
  by (induct m rule: xa_induct, simp_all add: hat_homU_append)

lemma iota_alpha0_remove_aux:
  "valuate (valuate (hat_homU (\<iota> \<alpha>0) m x')) 
 = valuate (concatU (valuate m) x')"
proof (induct m rule: xa_induct)
  case Nil
  then show ?case by (simp add: idU_def)
next
  case (Var x xs)
  then show ?case 
    apply (simp add: concatU_append hat_homU_append valuate_update_map_alpha map_alpha_distrib)
    apply (simp add: ignore_left_iota_alpha0 comp_left_neutral)
    done
next
  case (Alpha m xs)
  then show ?case 
    apply (simp add: concatU_append hat_homU_append valuate_update_map_alpha)
    apply (simp add: map_alpha_distrib ignore_left_inr_list)
    apply (simp add: ignore_left_hat_hom_iota_alpha0)
    done
qed


lemma iota_alpha0_remove:
  "valuate (valuate (hat_hom (hat_homU (\<iota> \<alpha>0) m) (hat_alpha inr_list u))) 
 = valuate (hat_hom (concatU (valuate m)) u)"
  by (induct u rule: xa_induct, simp_all add: iota_alpha0_remove_aux)

lemma hoge3:
  fixes u :: "('y + 'b) list"
  fixes m :: "('x + ('y, 'b) update) list"
  shows "valuate (hat_hom (H' (\<alpha>0, \<theta>)) (valuate (hat_hom (hat_homU (\<iota> (\<Delta>' (\<alpha>0, \<theta>))) m) (hat_alpha inr_list u))))
       = valuate (hat_hom (concatU (valuate (hat_hom \<theta> m))) u)"
  apply (simp add: hat_hom_valuate_hat_hom)
  apply (simp add: hat_homU_map_alpha)
  apply (simp add: update2hom_hat_alpha)
  apply (simp add: map_alpha_H'_iota_\<Delta>)
  apply (simp add: hat_homU_lem)
  

  apply (simp add: iota_alpha0_remove)
  done

lemma map_alpha_resolve_store_0:
  "hat_hom t (fst (scan u)) = fst (scan (hat_alpha (update2hom t) u))"
proof (induct u rule: xw_induct)
  case (Word w)
  then show ?case by (simp add: scan_word_simp hat_alpha_right_map hat_hom_def)
next
  case (VarWord x w u)
  then show ?case by (simp add: scan_last_simp hat_alpha_right_map)
qed

lemma length_scan_hat_alpha: "length (snd (scan (hat_alpha t u))) = length (snd (scan u))"
  by (induct u rule: xw_induct, simp_all add: hat_alpha_right_map scan_word_simp scan_last_simp)


lemma map_alpha_resolve_store_suc:
  "hat_hom t (nth_string' (d (y, Suc k)) (snd (scan u)) k)
 = nth_string' (hat_hom t (d (y, Suc k))) (snd (scan (hat_alpha (update2hom t) u))) k"
proof (induct u arbitrary: k rule: xw_induct)
  case (Word w)
  then show ?case by (simp add: scan_word_simp hat_alpha_right_map)
next
  case (VarWord x w u)
  then show ?case proof (induct k)
    case 0
    then show ?case by (simp add: scan_last_simp hat_alpha_right_map nth_string'_append length_scan_hat_alpha hat_hom_def)
  next
    case (Suc k)
    then show ?case apply (simp add: scan_last_simp hat_alpha_right_map) sorry
  qed
(*  then show ?case proof (cases "k < length (snd (scan u))")
    case True
    then show ?thesis
      by (simp add: scan_last_simp hat_alpha_right_map nth_string'_append length_scan_hat_alpha VarWord)
  next
    case False
    then show ?thesis proof (cases "k - length (snd (scan u))")
      case 0
      then show ?thesis
        apply (simp add: scan_last_simp hat_alpha_right_map nth_string'_append length_scan_hat_alpha )
    next
      case (Suc nat)
      then show ?thesis sorry
    qed
      thm VarWord
  qed
*)
qed


lemma map_alpha_resolve_store:
  "(t \<bullet> resolve_store d \<theta>) (y, k) = resolve_store (t \<bullet> d) (update2hom t \<star> \<theta>) (y, k)"
proof (cases k)
  case 0
  then show ?thesis by (simp add: resolve_store_def comp_def map_alpha_def map_alpha_resolve_store_0)
next
  case (Suc nat)
  then show ?thesis by (simp add: resolve_store_def comp_def map_alpha_def map_alpha_resolve_store_suc)
qed

lemma H'_assoc_string:
  "resolve_store (default_string x) (hat_homU (\<iota> \<alpha>) (hat_hom \<phi> u)) (y, k)
 = (H' (\<alpha>, \<phi>) \<bullet> resolve_store (default_string x) (hat_homU (\<iota> (\<Delta>' (\<alpha>, \<phi>))) u)) (y, k)"
proof -
  have "hat_homU (\<iota> \<alpha>) (hat_hom \<phi> u)
      = update2hom (H' (\<alpha>, \<phi>)) \<star> hat_homU (\<iota> (\<Delta>' (\<alpha>, \<phi>))) u"
    apply (simp add: hat_homU_map_alpha)
    apply (simp add: map_alpha_H'_iota_\<Delta>)
    apply (simp add: hat_homU_lem)
    done
  then show ?thesis
    apply (simp add: map_alpha_resolve_store)
   


lemma H'_assoc: "H' (\<alpha>, \<phi> \<bullet> \<psi>) = H' (\<alpha>, \<phi>) \<bullet> H' (\<Delta>' (\<alpha>, \<phi>), \<psi>)"
  sorry


lemma convert_\<delta>_hat:
  "SST.hat1 (convert_\<delta> msst) ((q, \<alpha>0), w) =
   (Monoid_SST.delta_hat msst (q, w), \<Delta>' (\<alpha>0, Monoid_SST.eta_hat msst (q, w)))"
proof (induct w arbitrary: q rule: rev_induct)
  case Nil
  then show ?case 
    apply (simp add: convert_\<delta>_def)
    apply (intro ext)
    apply (simp add: \<Delta>'_def idU_def \<iota>_def comp_right_neutral map_alpha_synthesize \<alpha>0_def idS_def)
    apply (simp add: resolve_shuffle_def synthesize_def synthesize_shuffle_def comp_def)
    apply (simp add: scan_def padding_def synthesize_store_def)
    done
next
  case (snoc a w)
  then show ?case by (simp add: delta_append eta_append comp_right_neutral  \<Delta>'_assoc convert_\<delta>_def)
qed

lemma nth_string_vars: "nth_string' [Inl (x, y, Suc k)] [(y, [Inl (x, y, Suc 0)])] k = [Inl (x, y, Suc k)]"
  by (induct k, simp_all)

lemma convert_\<eta>_hat_Nil:
  "idU (x, y, k) = H' (\<alpha>0, idU) (x, y, k)"
proof (cases k)
  case 0
  then show ?thesis
    apply (simp add: convert_\<delta>_def)
    apply (simp add: idU_def \<alpha>0_def idS_def H'_def)
    apply (simp add: \<iota>_def comp_right_neutral map_alpha_synthesize)
    unfolding resolve_store_def scan_def synthesize_def 
      synthesize_shuffle_def padding_def synthesize_store_def comp_def
    apply (simp add: \<alpha>0_def idS_def)
    done
next
  case (Suc k')
  then show ?thesis
    apply (simp add: convert_\<delta>_def)
    apply (simp add: \<Delta>'_def idU_def \<alpha>0_def idS_def H'_def)
    apply (simp add: \<iota>_def comp_right_neutral map_alpha_synthesize)
    unfolding resolve_store_def scan_def synthesize_def 
      synthesize_shuffle_def padding_def synthesize_store_def comp_def
    apply (simp add: \<alpha>0_def idS_def nth_string_vars)
    done
qed

lemma convert_\<eta>_hat:
  "SST.hat2 (convert_\<delta> msst) (convert_\<eta> msst) ((q0, \<alpha>0), w) =
   H' (\<alpha>0, Monoid_SST.eta_hat msst (q0, w))"
proof (induct w rule: rev_induct)
  case Nil
  then show ?case by (auto simp add: convert_\<eta>_hat_Nil) 
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
  show ?thesis proof (cases "MSST.final_string msst (hat1 (delta msst) (initial msst, w))")
    case None
    then show ?thesis
      by (simp add: convert_MSST_def SST.run_def Monoid_SST.run_def convert_final_def convert_\<delta>_hat Some1)
  next
    case Some2: (Some u)
    then show ?thesis
      apply (simp add: convert_MSST_def SST.run_def Monoid_SST.run_def convert_final_def convert_\<delta>_hat convert_\<eta>_hat Some1 del: comp_apply)
      apply (simp add: comp_def hoge3)
      done
  qed
qed

end



