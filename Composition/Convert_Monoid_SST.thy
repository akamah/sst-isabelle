(* Title:   Convert_Monoid_SST.thy
   Author:  Akama Hitoshi
*)

section \<open>Proof of convertion from a Monoid SST to a ordinary SST\<close>

theory Convert_Monoid_SST
  imports Main Sum_Type "../Core/Update" "../Core/SST" "../Core/Monoid_SST" "../Decomposition/Decompose_Update"
                         "../Type/Monoid_SST_Type" "Convert_Monoid_SST_Def" "Convert_Monoid_SST_Type_Misc"
begin

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



lemma H'_embed: "H' B (\<alpha>, \<theta>) \<bullet> Convert_Monoid_SST_Def.embed x = resolve_store B (hat_homU (\<iota> B \<alpha>) (\<theta> x))"
  by (auto simp add: comp_def H'_def)

lemma H'_const_Nil: "H' B (\<alpha>, \<theta>) \<bullet> const [] = const []"
  by (auto simp add: comp_def)



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

lemma ignore_left_iota_alpha0: "ignore_left \<star> \<iota> B \<alpha>0 x = idU"
proof -
  have 1: "concat o map ignore_left o embed x = (\<lambda>(y, k). [])"
    by auto
  show ?thesis 
    by (simp add: \<iota>_def synthesize_store_def \<alpha>0_def map_alpha_synthesize 1 synthesize_idU)
qed


lemma ignore_left_hat_homU_iota_alpha0: "ignore_left \<star> hat_homU (\<iota> B \<alpha>0) m = concatU (valuate m)"
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
  "valuate (valuate (hat_homU (\<iota> B \<alpha>0) m x')) 
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
    apply (simp add: ignore_left_hat_homU_iota_alpha0)
    done
qed


lemma iota_alpha0_remove:
  "valuate (valuate (hat_hom (hat_homU (\<iota> B \<alpha>0) m) (hat_alpha inr_list u))) 
 = valuate (hat_hom (concatU (valuate m)) u)"
  by (induct u rule: xa_induct, simp_all add: iota_alpha0_remove_aux)




lemma length_scan_hat_alpha: "length_scanned (scan (hat_alpha t u)) = length_scanned (scan u)"
  by (induct u rule: xw_induct, simp_all add: hat_alpha_right_map)


lemma map_alpha_resolve_store_aux: 
  "hat_hom t (nth_string (scan u) k)
 = nth_string (scan (hat_alpha (update2hom t) u)) k"
proof (induct u arbitrary: k rule: xw_induct)
  case (Word w)
  then show ?case by (simp add: hat_alpha_right_map nth_string_Nil hat_hom_def)
next
  case (VarWord x w u)
  then show ?case
    by (auto simp add: hat_alpha_right_map nth_string_append_last length_scan_hat_alpha hat_hom_def)
qed

lemma map_alpha_resolve_store:
  "(t \<bullet> resolve_store B \<theta>) (y, k) = resolve_store B (update2hom t \<star> \<theta>) (y, k)"
  by (cases "enum_to_nat k", simp_all add: resolve_store_def comp_def map_alpha_def map_alpha_resolve_store_aux)


lemma [simp]: "scan [Inl y] = ([], [(y, [])])"
  by (simp add: scan_def)


lemma scan_valuate: "fst (scan (hat_alpha ignore_left u)) = valuate (fst (scan u))"
proof (induct u rule: xw_induct)
  case (Word w)
  then show ?case by (simp add: hat_alpha_right_map valuate_ignore_left)
next
  case (VarWord x w u)
  then show ?case by (simp add: hat_alpha_right_map)
qed


fun map_scanned' :: "('a \<Rightarrow> 'b list) \<Rightarrow> ('y \<times> 'a list) list \<Rightarrow> ('y \<times> 'b list) list" where
  "map_scanned' f [] = []" |
  "map_scanned' f ((y, as) # yas) = (y, concat (map f as)) # map_scanned' f yas"

definition map_scanned :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a list \<times> ('y \<times> 'a list) list \<Rightarrow> 'b list \<times> ('y \<times> 'b list) list" where
  "map_scanned f = (\<lambda>(w, xas). (concat (map f w), map_scanned' f xas))"

lemma map_scanned_Nil_simp[simp]: "map_scanned f (w, []) = (concat (map f w), [])"
  by (simp add: map_scanned_def)

lemma map_scanned_pair_simp[simp]:
  "map_scanned f (sc @@@ [(x, as)])
 = map_scanned f sc @@@ [(x, concat (map f as))]"
  by (induct sc rule: scanned_induct, simp_all add: append_scanned_simp map_scanned_def)

lemma length_map_scanned: "length_scanned (map_scanned f sc) = length_scanned sc"
  by (induct sc rule: scanned_induct, simp_all add: append_scanned_simp map_scanned_def)

lemma map_scanned_hat_alpha: "scan (hat_alpha f u) = map_scanned f (scan u)"
  by (induct u rule: xw_induct, simp_all add: hat_alpha_right_map)


lemma nth_string_valuate: 
  "valuate (nth_string (scan u) n)
 = nth_string (map_scanned ignore_left (scan u)) n"
proof (induct u arbitrary: n rule: xw_induct)
  case (Word w)
  then show ?case proof (cases n)
    case 0
    then show ?thesis by (simp add: valuate_ignore_left)
  next
    case (Suc nat)
    then show ?thesis by (simp add: hat_alpha_right_map nth_string_pos_Nil)
  qed
next
  case (VarWord x w u)
  then show ?case proof (cases n)
    case 0
    then show ?thesis using VarWord
      by (simp add: valuate_ignore_left nth_string_append_first)
  next
    case (Suc nat)
    then show ?thesis using VarWord
      by (auto simp add: valuate_ignore_left nth_string_append_last length_scan_hat_alpha length_map_scanned)
  qed
qed

lemma hat_alpha_synthesize:
  "hat_alpha t (synthesize B (s, a) y) = synthesize B (s, concat o map t o a) y"
proof -
  have "\<And>y'. (hat_alpha t \<circ> synthesize B (s, a)) y = synthesize B (s, concat \<circ> map t \<circ> a) y"
    by (simp add: map_alpha_synthesize[simplified map_alpha_def])
  then show ?thesis by simp
qed

lemma concat_map_ignore_left_embed: "concat \<circ> map ignore_left \<circ> Convert_Monoid_SST_Def.embed x = const []"
  by (rule ext, simp)


lemma cm_synthesize_store_const_is_inl: "list_all is_inl (concat (map (synthesize_store B (const [])) ps))"
  by (induct ps rule: xa_induct, simp_all add: synthesize_store_def)


lemma list_all_is_inl_map_Inr:
  assumes "list_all is_inl (map Inr bs)"
  shows "bs = []"
  using assms by (induct bs, simp_all)

lemma nth_string_scan_is_inl:
  assumes "list_all is_inl u"
  shows "nth_string (scan u) k = []"
using assms proof (induct u arbitrary: k rule: xw_induct)
  case (Word w)
  then have "w = []" by (simp add: list_all_is_inl_map_Inr)
  then show ?case by (cases k, simp_all)
next
  case (VarWord x w u)
  have "w = []" using VarWord.prems list_all_is_inl_map_Inr by auto
  then show ?case using VarWord by (simp add: nth_string_append_last)
qed


lemma nth_string_map_scanned_ignore_left:
  "nth_string (map_scanned ignore_left (scan (\<iota> B \<alpha> x y))) k = []"
  apply (simp add: comp_def map_scanned_hat_alpha[symmetric] \<iota>_def hat_alpha_synthesize concat_map_ignore_left_embed)
  apply (simp add: synthesize_def synthesize_store_def synthesize_shuffle_def comp_def hat_hom_left_concat_map)
  apply (simp add: nth_string_scan_is_inl cm_synthesize_store_const_is_inl)
  done

lemma valuate_H'_Nil_var: "valuate (H' B (\<alpha>, idU) (x, y, k)) = []"
  apply (simp add: H'_def idU_def comp_right_neutral)
  apply (simp add: resolve_store_def nth_string_valuate nth_string_map_scanned_ignore_left)
  done


lemma valuate_H'_Nil: "valuate (hat_hom (H' B (\<alpha>, idU)) u) = valuate u"
proof (induct u rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case by (cases x, simp add: valuate_H'_Nil_var)
next
  case (Alpha a xs)
  then show ?case by simp
qed

(* SST.eta_hat msst (q, w) *)
thm hat_homU_iota_bounded_copy
thm resolve_inverse
lemma map_alpha_H'_iota_\<Delta>:
  fixes x :: "'x"
  fixes \<alpha> :: "'x \<Rightarrow> 'y::enum shuffle"
  fixes \<theta> :: "('x, ('y, 'b) update) update"
  assumes "boundedness B k"
  assumes "is_type msst \<gamma>"
  assumes "bounded_copy_type k msst \<gamma>"
  assumes "reachable (convert_MSST B msst) (q, \<alpha>)"
  shows "map_alpha (update2hom (H' B (\<alpha>, SST.eta_hat msst (q, w)))) o \<iota> B (\<Delta>' B (\<alpha>, SST.eta_hat msst (q, w))) 
       = hat_homU (\<iota> B \<alpha>) o SST.eta_hat msst (q, w)"
  apply (rule ext)
  apply (simp add: \<iota>_def map_alpha_synthesize comp_def[symmetric] hat_hom_def[symmetric] H'_embed \<Delta>'_def)
  apply (rule resolve_inverse)
  apply (rule hat_homU_iota_bounded_copy)
  apply (rule assms)+
  done


lemma hat_homU_iota:
  fixes \<alpha> :: "'x \<Rightarrow> 'y::enum shuffle"
  assumes "boundedness B k"
  assumes "is_type msst \<gamma>"
  assumes "bounded_copy_type k msst \<gamma>"
  assumes "reachable (convert_MSST B msst) (q, \<alpha>)"
  shows "hat_homU (\<iota> B \<alpha>) (hat_hom (SST.eta_hat msst (q, w)) u)
       = update2hom (H' B (\<alpha>, SST.eta_hat msst (q, w))) \<star> hat_homU (\<iota> B (\<Delta>' B (\<alpha>, SST.eta_hat msst (q, w)))) u"
  apply (simp add: hat_homU_map_alpha hat_homU_lem map_alpha_H'_iota_\<Delta>[OF assms])
  done

lemma H'_assoc_string:
  fixes \<alpha> :: "'x \<Rightarrow> 'y::enum shuffle"
  assumes "boundedness B k"
  assumes "is_type msst \<gamma>"
  assumes "bounded_copy_type k msst \<gamma>"
  assumes "reachable (convert_MSST B msst) (q, \<alpha>)"
  shows "resolve_store B (hat_homU (\<iota> B \<alpha>) (hat_hom (SST.eta_hat msst (q, w)) u)) (y, e)
       = (H' B (\<alpha>, SST.eta_hat msst (q, w)) \<bullet> resolve_store B (hat_homU (\<iota> B (\<Delta>' B (\<alpha>, SST.eta_hat msst (q, w)))) u)) (y, e)"
  apply (simp add: hat_homU_iota[OF assms] map_alpha_resolve_store H'_const_Nil)
  done

lemma H'_assoc:
  fixes \<alpha> :: "'x \<Rightarrow> 'y::enum shuffle"
  assumes "boundedness B k"
  assumes "is_type msst \<gamma>"
  assumes "bounded_copy_type k msst \<gamma>"
  assumes "reachable (convert_MSST B msst) (q, \<alpha>)"
  shows "H' B (\<alpha>, SST.eta_hat msst (q, w) \<bullet> \<psi>)
       = H' B (\<alpha>, SST.eta_hat msst (q, w)) \<bullet> H' B (\<Delta>' B (\<alpha>, SST.eta_hat msst (q, w)), \<psi>)"
proof -
  have "\<And>x y e. H' B (\<alpha>, SST.eta_hat msst (q, w) \<bullet> \<psi>) (x, y, e) 
              = (H' B (\<alpha>, SST.eta_hat msst (q, w)) \<bullet> H' B (\<Delta>' B (\<alpha>, SST.eta_hat msst (q, w)), \<psi>)) (x, y, e)"
    by (simp add: comp_def H'_assoc_string[OF assms] H'_simp2)
  then show ?thesis by auto
qed

lemma convert_\<eta>_hat_valuate:
  assumes "boundedness B k"
  assumes "is_type msst \<gamma>"
  assumes "bounded_copy_type k msst \<gamma>"
  assumes r: "reachable (convert_MSST B msst) (q, \<alpha>)"
  shows   "valuate (hat_hom (SST.hat2 (convert_\<delta> B msst) (convert_\<eta> B msst) ((q, \<alpha>), w)) u)
         = valuate (hat_hom (H' B (\<alpha>, eta_hat msst (q, w))) u)"
using r proof (induct w arbitrary: u q \<alpha> rule: rev_induct)
  case Nil
  then show ?case by (simp add: convert_\<delta>_def valuate_H'_Nil)
next
  case (snoc a w)
  then show ?case (is "?lhs = ?rhs") proof -
    assume reach: "reachable (convert_MSST B msst) (q, \<alpha>)"
    have "valuate (hat_hom (SST.hat2 (convert_\<delta> B msst) (convert_\<eta> B msst) ((q, \<alpha>), w @ [a])) u)
        = valuate (hat_hom (SST.hat2 (convert_\<delta> B msst) (convert_\<eta> B msst) ((q, \<alpha>), w))
                           (hat_hom (convert_\<eta> B msst (hat1 (convert_\<delta> B msst) ((q, \<alpha>), w), a)) u))"
      apply (simp add: eta_append idU_def comp_right_neutral)
      apply (simp add: comp_def comp_lem)
      done
    also have "... = valuate (hat_hom (H' B (\<alpha>, eta_hat msst (q, w)))
                                      (hat_hom (convert_\<eta> B msst (hat1 (convert_\<delta> B msst) ((q, \<alpha>), w), a)) u))"
      by (simp add: snoc)
    also have "... = valuate (hat_hom (H' B (\<alpha>, eta_hat msst (q, w)))
                                    (hat_hom (H' B (\<Delta>' B (\<alpha>, eta_hat msst (q, w)),
                                                  SST.eta msst (delta_hat msst (q, w), a))) u))"
      by (simp add: convert_\<delta>_hat convert_\<eta>_def)
    also have "... = ?rhs"
      apply (simp add: eta_append comp_right_neutral)
      apply (simp add: H'_assoc[OF assms(1) assms(2) assms(3) reach])
      thm H'_assoc[OF assms]
      apply (simp add: comp_def comp_lem del: Fun.comp_apply)
      done
    finally show ?thesis .
  qed
qed


lemma the_last_step:
  fixes u :: "('y::enum + 'b) list"
  fixes m :: "('x + ('y, 'b) update) list"
  assumes "boundedness B k"
  assumes "is_type msst \<gamma>"
  assumes "bounded_copy_type k msst \<gamma>"
  shows "valuate (hat_hom (H' B (\<alpha>0, SST.eta_hat msst (initial msst, w)))
          (valuate (hat_hom (hat_homU (\<iota> B (\<Delta>' B (\<alpha>0, SST.eta_hat msst (initial msst, w)))) m) (hat_alpha inr_list u))))
       = valuate (hat_hom (concatU (valuate (hat_hom (SST.eta_hat msst (initial msst, w)) m))) u)"
proof -
  have *: "reachable (convert_MSST B msst) (initial msst, \<alpha>0)"
    unfolding reachable_def convert_MSST_def by (rule exI[where x="[]"], simp)
  show ?thesis
    apply (simp add: hat_hom_valuate_hat_hom)
    apply (simp add: hat_homU_map_alpha)
    apply (simp add: update2hom_hat_alpha)
    apply (simp add: map_alpha_H'_iota_\<Delta>[OF assms *])
    apply (simp add: hat_homU_lem)
    apply (simp add: iota_alpha0_remove)
  done
qed


theorem MSST_can_convert:
  assumes assm_k_bounded: "boundedness B k"
  assumes assm_is_type: "is_type msst \<gamma>"
  assumes assm_bounded_type: "bounded_copy_type k msst \<gamma>"
  shows "SST.run (convert_MSST B msst) w = Monoid_SST.run msst w"
proof (cases "final_update msst (hat1 (delta msst) (initial msst, w))")
  case None
  then show ?thesis
    by (simp add: convert_MSST_def SST.run_def Monoid_SST.run_def convert_final_def convert_\<delta>_hat)
next
  case Some1: (Some m)
  show ?thesis proof (cases "final_string msst (hat1 (delta msst) (initial msst, w))")
    case None
    then show ?thesis
      by (simp add: convert_MSST_def SST.run_def Monoid_SST.run_def convert_final_def convert_\<delta>_hat Some1)
  next
    case Some2: (Some u)
    have reach0: "reachable (convert_MSST B msst) (initial msst, \<alpha>0)"
      unfolding reachable_def convert_MSST_def by (rule exI[where x="[]"], simp)
    show ?thesis using Some2
      apply (simp add: convert_MSST_def SST.run_def Monoid_SST.run_def convert_final_def convert_\<delta>_hat Some1)
      apply (simp add: convert_\<eta>_hat_valuate[OF assms reach0] comp_def)
      apply (simp add: comp_def the_last_step[OF assms])
      done
  qed
qed

end
