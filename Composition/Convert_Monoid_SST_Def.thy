theory Convert_Monoid_SST_Def
  imports Main "../Core/Update" "../Core/SST" "../Core/Monoid_SST" "../Single_Use/Single_Use" "../Decomposition/Decompose_Update"
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

definition \<iota> :: "'k::enum boundedness \<Rightarrow> ('x \<Rightarrow> 'y::enum shuffle) \<Rightarrow> 'x 
              \<Rightarrow> ('y, 'x \<times> ('y, 'k) index + 'b) update" where
  "\<iota> B \<alpha> x = synthesize B (\<alpha> x, embed x)"


definition \<Delta>' :: "'k::enum boundedness \<Rightarrow> ('x \<Rightarrow> 'y::enum shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<Rightarrow> 'y shuffle)" where
  "\<Delta>' B = (\<lambda>(\<alpha>, \<theta>). \<lambda>x. resolve_shuffle (hat_homU (\<iota> B \<alpha>) (\<theta> x)))"


definition H' :: "'k::enum boundedness \<Rightarrow> ('x \<Rightarrow> 'y::enum shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<times> ('y, 'k) index, 'b) update" where
  "H' B = (\<lambda>(\<alpha>, \<theta>). \<lambda>(x, y'). resolve_store B (hat_homU (\<iota> B \<alpha>) (\<theta> x)) y')"

lemma H'_simp2: "H' B (\<alpha>, \<theta>) (x, y') = resolve_store B (hat_homU (\<iota> B \<alpha>) (\<theta> x)) y'"
  by (simp add: H'_def)



subsection \<open>Construction\<close>

definition \<alpha>0 :: "'x \<Rightarrow> 'y shuffle" where
  "\<alpha>0 x = idS"


definition convert_\<delta> :: "'i::enum boundedness \<Rightarrow> ('q, 'x, 'y::enum, 'a, 'b) MSST \<Rightarrow> ('q \<times> ('x \<Rightarrow> 'y shuffle), 'a) trans" where
  "convert_\<delta> B msst =
     (\<lambda>((q1, f), a). (delta msst (q1, a), \<Delta>' B (f, eta msst (q1, a))))"

definition convert_\<eta> :: "'i::enum boundedness \<Rightarrow> ('q, 'x, 'y::enum, 'a, 'b) MSST \<Rightarrow>
                         ('q \<times> ('x \<Rightarrow> 'y shuffle), 'x \<times> ('y, 'i) index, 'a, 'b) updator" where
  "convert_\<eta> B msst = (\<lambda>((q, \<alpha>), b). H' B (\<alpha>, eta msst (q, b)))"

definition convert_final :: "'i::enum boundedness \<Rightarrow> ('q, 'x, 'y::enum, 'a, 'b) MSST \<Rightarrow>
   ('q \<times> ('x \<Rightarrow> 'y shuffle) \<Rightarrow> ('x \<times> ('y, 'i) index + 'b) list option)" where
  "convert_final B msst = (\<lambda>(q, \<alpha>).
     (case final_update msst q of
        Some u \<Rightarrow> (case final_string msst q of
          Some v \<Rightarrow> Some (valuate (hat_hom (hat_homU (\<iota> B \<alpha>) u) (hat_alpha inr_list v))) |
          None \<Rightarrow> None) |
        None \<Rightarrow> None))"

lemma convert_\<delta>_simp: "convert_\<delta> B msst ((q1, f), a) = (delta msst (q1, a), \<Delta>' B (f, eta msst (q1, a)))"
  by (simp add: convert_\<delta>_def)

lemma convert_\<eta>_simp: "convert_\<eta> B msst ((q1, f), a) = H' B (f, eta msst (q1, a))"
  by (simp add: convert_\<eta>_def)

definition convert_MSST :: "'i::enum boundedness \<Rightarrow> ('q, 'x, 'y::enum, 'a, 'b) MSST \<Rightarrow>
                            ('q \<times> ('x \<Rightarrow> 'y shuffle), 'x \<times> ('y, 'i) index, 'a, 'b) SST" where
  "convert_MSST B msst = \<lparr>
    states = states msst \<times> {m1. True},
    initial = (initial msst, \<alpha>0),
    delta       = convert_\<delta> B msst,
    variables = undefined,
    eta         = convert_\<eta> B msst,
    final       = convert_final B msst
  \<rparr>"


end
