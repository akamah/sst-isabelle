(* Title:   Convert_Monoid_SST.thy
   Author:  Akama Hitoshi
*)

section \<open>Convert a Monoid SST to a ordinary SST\<close>

theory Convert_Monoid_SST
  imports Main Sum_Type "../Core/Update" "../Core/SST" "../Core/Monoid_SST" "../Decomposition/Decompose_Update"
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

definition \<iota> :: "('x \<Rightarrow> 'y shuffle) \<Rightarrow> 'x \<Rightarrow> ('y, 'x \<times> ('y, 'i::enum) index + 'b) update" where
  "\<iota> \<alpha> x = synthesize (\<alpha> x, embed x)"


definition \<Delta>' :: "('x \<Rightarrow> 'y shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<Rightarrow> 'y shuffle)" where
  "\<Delta>' = (\<lambda>(\<alpha>, \<theta>). \<lambda>x. resolve_shuffle (hat_homU (\<iota> \<alpha>) (\<theta> x)))"


definition H' :: "('x \<Rightarrow> 'y shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<times> 'y index, 'b) update" where
  "H' = (\<lambda>(\<alpha>, \<theta>). \<lambda>(x, y'). resolve_store (const []) (hat_homU (\<iota> \<alpha>) (\<theta> x)) y')"

lemma H'_simp2: "H' (\<alpha>, \<theta>) (x, y') = resolve_store (const []) (hat_homU (\<iota> \<alpha>) (\<theta> x)) y'"
  by (simp add: H'_def)


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
    by (simp add: resolve_shuffle_distrib hat_homU_append \<iota>_def synthesize_inverse_shuffle)
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
     (\<lambda>((q1, f), a). (delta msst (q1, a), \<Delta>' (f, eta msst (q1, a))))"

definition convert_\<eta> :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow>
                         ('q \<times> ('x \<Rightarrow> 'y shuffle), 'x \<times> 'y index, 'a, 'b) updator" where
  "convert_\<eta> msst = (\<lambda>((q, \<alpha>), b). H' (\<alpha>, eta msst (q, b)))"

definition convert_final :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow>
   ('q \<times> ('x \<Rightarrow> 'y shuffle) \<Rightarrow> ('x \<times> 'y index + 'b) list option)" where
  "convert_final msst = (\<lambda>(q, \<alpha>).
     (case final_update msst q of
        Some u \<Rightarrow> (case final_string msst q of
          Some v \<Rightarrow> Some (valuate (hat_hom (hat_homU (\<iota> \<alpha>) u) (hat_alpha inr_list v))) |
          None \<Rightarrow> None) |
        None \<Rightarrow> None))"

lemma convert_\<delta>_simp: "convert_\<delta> msst ((q1, f), a) = (delta msst (q1, a), \<Delta>' (f, eta msst (q1, a)))"
  by (simp add: convert_\<delta>_def)

lemma convert_\<eta>_simp: "convert_\<eta> msst ((q1, f), a) = H' (f, eta msst (q1, a))"
  by (simp add: convert_\<eta>_def)

definition convert_MSST :: "('q, 'x, 'y, 'a, 'b) MSST \<Rightarrow>
                            ('q \<times> ('x \<Rightarrow> 'y shuffle), 'x \<times> 'y index, 'a, 'b) SST" where
  "convert_MSST msst = \<lparr>
    states = states msst \<times> {m1. True},
    initial = (initial msst, \<alpha>0),
    delta       = convert_\<delta> msst,
    variables = variables msst \<times> MSST.variables2 msst \<times> (UNIV::nat set),
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



lemma H'_embed: "H' (\<alpha>, \<theta>) \<bullet> embed x = resolve_store (const []) (hat_homU (\<iota> \<alpha>) (\<theta> x))"
  by (auto simp add: comp_def H'_def)

lemma H'_const_Nil: "H' (\<alpha>, \<theta>) \<bullet> const [] = const []"
  by (auto simp add: comp_def)


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

lemma length_scan_hat_alpha: "length_scanned (scan (hat_alpha t u)) = length_scanned (scan u)"
  by (induct u rule: xw_induct, simp_all add: hat_alpha_right_map)


lemma map_alpha_resolve_store_aux: "hat_hom t (nth_string s (scan u) k)
 = nth_string (hat_hom t s) (scan (hat_alpha (update2hom t) u)) k"
proof (induct u arbitrary: k rule: xw_induct)
  case (Word w)
  then show ?case by (simp add: hat_alpha_right_map nth_string_Nil hat_hom_def)
next
  case (VarWord x w u)
  then show ?case
    by (auto simp add: hat_alpha_right_map nth_string_append_last length_scan_hat_alpha hat_hom_def)
qed

lemma map_alpha_resolve_store:
  "(t \<bullet> resolve_store d \<theta>) (y, k) = resolve_store (t \<bullet> d) (update2hom t \<star> \<theta>) (y, k)"
  by (cases k, simp_all add: resolve_store_def comp_def map_alpha_def map_alpha_resolve_store_aux)


lemma "resolve_store (embed x) (hat_homU (\<iota> \<alpha>) (hat_hom \<phi> u)) (y, k)
     = resolve_store (H' (\<alpha>, \<phi>) \<bullet> embed x) (hat_homU (\<iota> \<alpha>) (hat_hom \<phi> u)) (y, k)"
  oops

lemma hat_homU_iota:
  "hat_homU (\<iota> \<alpha>) (hat_hom \<phi> u)
 = update2hom (H' (\<alpha>, \<phi>)) \<star> hat_homU (\<iota> (\<Delta>' (\<alpha>, \<phi>))) u"
  by (simp add: hat_homU_map_alpha  map_alpha_H'_iota_\<Delta> hat_homU_lem)


lemma H'_assoc_string:
  "resolve_store (const []) (hat_homU (\<iota> \<alpha>) (hat_hom \<phi> u)) (y, k)
 = (H' (\<alpha>, \<phi>) \<bullet> resolve_store (const []) (hat_homU (\<iota> (\<Delta>' (\<alpha>, \<phi>))) u)) (y, k)"
  by (simp add: hat_homU_iota map_alpha_resolve_store H'_const_Nil)

lemma H'_assoc: "H' (\<alpha>, \<phi> \<bullet> \<psi>) = H' (\<alpha>, \<phi>) \<bullet> H' (\<Delta>' (\<alpha>, \<phi>), \<psi>)"
  by (auto simp add: comp_def H'_assoc_string H'_simp2)


lemma "let \<phi> = (\<lambda>x :: nat. []) in
  let \<psi> = (\<lambda>x :: nat. [Inr (\<lambda>x. [])]) in
  \<Delta>'(\<alpha>0, \<phi>) = \<alpha>0"
  apply (simp add: Let_def)
  apply (intro ext)
  apply (simp add: comp_def \<Delta>'_def idU_def resolve_shuffle_def \<alpha>0_def idS_def)
  done

lemma [simp]: "scan [Inl y] = ([], [(y, [])])"
  by (simp add: scan_def)


lemma \<Delta>'_id: "\<Delta>' (\<alpha>, idU) = \<alpha>"
  apply (rule ext)
  apply (simp add: \<Delta>'_def idU_def comp_right_neutral)
  apply (simp add: resolve_shuffle_def \<iota>_def synthesize_inverse_shuffle)
  done

lemma convert_\<delta>_hat:
  "hat1 (convert_\<delta> msst) ((q, \<alpha>), w) =
   (delta_hat msst (q, w), \<Delta>' (\<alpha>, eta_hat msst (q, w)))"
proof (induct w arbitrary: q rule: rev_induct)
  case Nil
  then show ?case by (simp add: convert_\<delta>_def \<Delta>'_id)
next
  case (snoc a w)
  then show ?case by (simp add: eta_append comp_right_neutral  \<Delta>'_assoc convert_\<delta>_def)
qed

lemma nth_string_vars: "nth_string [Inl (x, y, Suc k)] ([Inl (x, y, Suc 0)], []) k = [Inl (x, y, Suc k)]"
  by (induct k, simp_all)


(* (* I think this lemma is old one *)
lemma convert_\<eta>_hat_Nil:
  "idU (x, y, k) = H' (\<alpha>0, idU) (x, y, k)"
proof (cases k)
  case 0
  then show ?thesis
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

*)

(* also, this will not hold *)
(* 
lemma convert_\<eta>_hat:
  "SST.hat2 (convert_\<delta> msst) (convert_\<eta> msst) ((q0, \<alpha>0), w) =
   H' (\<alpha>0, Monoid_SST.eta_hat msst (q0, w))"
proof (induct w rule: rev_induct)
  case Nil
  then show ?case by (auto simp add: convert_\<eta>_hat_Nil) 
next
  case (snoc a w)
  then show ?case
    apply (simp add: delta_append eta_append comp_right_neutral convert_\<eta>_def convert_\<delta>_hat)
    apply (simp add: H'_assoc)
    done
qed
*)

lemma all_variable_map_Inl: "List.list_all is_inl (map Inl xs)"
  by (induct xs, simp_all)

lemma "List.list_all is_inl (synthesize_shuffle \<theta> x)"
  by (simp add: synthesize_shuffle_def all_variable_map_Inl)


term "ignore_left \<star> (\<theta> :: ('y, 'z + 'b) update)"


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
  "valuate (nth_string w (scan u) n)
 = nth_string (valuate w) (map_scanned ignore_left (scan u)) n"
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
  "hat_alpha t (synthesize (s, a) y) = synthesize (s, concat o map t o a) y"
proof -
  have "\<And>y'. (hat_alpha t \<circ> synthesize (s, a)) y = synthesize (s, concat \<circ> map t \<circ> a) y"
    by (simp add: map_alpha_synthesize[simplified map_alpha_def])
  then show ?thesis by simp
qed

lemma concat_map_ignore_left_embed: "concat \<circ> map ignore_left \<circ> Convert_Monoid_SST.embed x = const []"
  by (rule ext, simp)


lemma cm_synthesize_store_const_is_inl: "list_all is_inl (concat (map (synthesize_store (const [])) ps))"
  by (induct ps rule: xa_induct, simp_all add: synthesize_store_def)


lemma list_all_is_inl_map_Inr:
  assumes "list_all is_inl (map Inr bs)"
  shows "bs = []"
  using assms by (induct bs, simp_all)

lemma nth_string_scan_is_inl:
  assumes "list_all is_inl u"
  shows "nth_string [] (scan u) k = []"
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
  "nth_string [] (map_scanned ignore_left (scan (\<iota> \<alpha> x y))) k = []"
  apply (simp add: comp_def map_scanned_hat_alpha[symmetric] \<iota>_def hat_alpha_synthesize concat_map_ignore_left_embed)
  apply (simp add: synthesize_def synthesize_store_def synthesize_shuffle_def comp_def hat_hom_left_concat_map)
  apply (simp add: nth_string_scan_is_inl cm_synthesize_store_const_is_inl)
  done

lemma valuate_H'_Nil_var: "valuate (H' (\<alpha>, idU) (x, y, k)) = []"
  apply (simp add: H'_def idU_def comp_right_neutral)
  apply (simp add: resolve_store_def nth_string_valuate nth_string_map_scanned_ignore_left)
  done


lemma valuate_H'_Nil: "valuate (hat_hom (H' (\<alpha>, idU)) u) = valuate u"
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


lemma convert_\<eta>_hat_valuate:
  "valuate (hat_hom (SST.hat2 (convert_\<delta> msst) (convert_\<eta> msst) ((q, \<alpha>), w)) u) =
   valuate (hat_hom (H' (\<alpha>, eta_hat msst (q, w))) u)"
proof (induct w arbitrary: u q \<alpha> rule: rev_induct)
  case Nil
  then show ?case by (simp add: convert_\<delta>_def valuate_H'_Nil)
next
  case (snoc a w)
  show ?case (is "?lhs = ?rhs") proof -
    have "valuate (hat_hom (SST.hat2 (convert_\<delta> msst) (convert_\<eta> msst) ((q, \<alpha>), w @ [a])) u)
        = valuate (hat_hom (SST.hat2 (convert_\<delta> msst) (convert_\<eta> msst) ((q, \<alpha>), w))
                           (hat_hom (convert_\<eta> msst (hat1 (convert_\<delta> msst) ((q, \<alpha>), w), a)) u))"
      apply (simp add: eta_append idU_def comp_right_neutral)
      apply (simp add: comp_def comp_lem)
      done
    also have "... = valuate (hat_hom (H' (\<alpha>, eta_hat msst (q, w)))
                                      (hat_hom (convert_\<eta> msst (hat1 (convert_\<delta> msst) ((q, \<alpha>), w), a)) u))"
      by (simp add: snoc)
    also have "... = valuate (hat_hom (H' (\<alpha>, eta_hat msst (q, w)))
                                    (hat_hom (H' (\<Delta>' (\<alpha>, eta_hat msst (q, w)),
                                                  SST.eta msst (delta_hat msst (q, w), a))) u))"
      by (simp add: convert_\<delta>_hat convert_\<eta>_def)
    also have "... = ?rhs"
      apply (simp add: eta_append H'_assoc comp_right_neutral)
      apply (simp add: comp_def comp_lem del: Fun.comp_apply)
      done
    finally show ?thesis .
  qed
qed




theorem MSST_can_convert:
  "SST.run (convert_MSST msst) w = Monoid_SST.run msst w"
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
    then show ?thesis
      apply (simp add: convert_MSST_def SST.run_def Monoid_SST.run_def convert_final_def convert_\<delta>_hat Some1)
      apply (simp add: convert_\<eta>_hat_valuate comp_def)
      apply (simp add: comp_def hoge3)
      done
  qed
qed

end
