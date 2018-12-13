theory Convert_Monoid_SST_Def
  imports Main "../Core/Update" "../Core/SST" "../Core/Monoid_SST" "../Single_Use/Single_Use" "../Decomposition/Decompose_Update" "../Decomposition/Shuffle"
begin


subsection \<open>Definition of another strange Transducer\<close>

definition update2homU ::
  "('x \<Rightarrow> ('y, 'z + 'b) update) \<Rightarrow> 
   ('x + ('y, 'b) update) \<Rightarrow>
   ('y, 'z + 'b) update"where
  "update2homU \<phi> = fold_sum \<phi> (map_alpha inr_list)"

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


fun Rep_alpha :: "'k::enum boundedness \<Rightarrow> ('x \<Rightarrow> ('k, 'y::enum) bc_shuffle) \<Rightarrow> ('x \<Rightarrow> 'y shuffle)" where
  "Rep_alpha B \<beta> x = Rep_bc_shuffle (\<beta> x)"

fun Abs_alpha :: "'k::enum boundedness \<Rightarrow> ('x \<Rightarrow> 'y shuffle ) \<Rightarrow> ('x \<Rightarrow> ('k, 'y::enum) bc_shuffle)" where
  "Abs_alpha B \<alpha> x = Abs_bc_shuffle (\<alpha> x)"


lemma Abs_alpha_inverse:
  assumes "boundedness (B :: 'k::enum boundedness) k"
  assumes "\<forall>x. bounded_shuffle k (\<alpha> x)"
  shows "Rep_alpha B (Abs_alpha B \<alpha>) = \<alpha>"
  using assms by (auto simp add: Abs_bc_shuffle_inverse boundedness_def)  

lemma Rep_alpha_inverse:
  shows "Abs_alpha B (Rep_alpha B \<beta>) = \<beta>"
  by (auto simp add: Rep_bc_shuffle_inverse)

lemma Rep_alpha:
  fixes B :: "'k::enum boundedness"
  shows "\<And>x. bounded_shuffle (length (Enum.enum :: 'k list)) (Rep_alpha B \<beta> x)"
  using Rep_bc_shuffle
  by simp

fun embed_single :: "'x \<Rightarrow> 'y \<Rightarrow> ('x \<times> 'y + 'b)" where
  "embed_single x y = Inl (x, y)"

fun embed :: "'x \<Rightarrow> 'y \<Rightarrow> ('x \<times> 'y + 'b) list" where
  "embed x y = [embed_single x y]"

definition \<iota> :: "'k::enum boundedness \<Rightarrow> ('x \<Rightarrow> 'y::enum shuffle) \<Rightarrow> 'x 
              \<Rightarrow> ('y, 'x \<times> ('y, 'k) index + 'b) update" where
  "\<iota> B \<alpha> x = synthesize B (\<alpha> x, embed x)"


definition \<Delta>' :: "'k::enum boundedness \<Rightarrow> ('x \<Rightarrow> ('k, 'y::enum) bc_shuffle, ('x, ('y, 'b) update) update) trans" where
  "\<Delta>' B = (\<lambda>(\<beta>, \<theta>). Abs_alpha B (\<lambda>x. resolve_shuffle (hat_homU (\<iota> B (Rep_alpha B \<beta>)) (\<theta> x))))"


definition H' :: "'k::enum boundedness \<Rightarrow> ('x \<Rightarrow> ('k, 'y::enum) bc_shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<times> ('y, 'k) index, 'b) update" where
  "H' B = (\<lambda>(\<beta>, \<theta>). \<lambda>(x, y'). resolve_store B (hat_homU (\<iota> B (Rep_alpha B \<beta>)) (\<theta> x)) y')"

lemma H'_simp2: "H' B (\<beta>, \<theta>) (x, y') = resolve_store B (hat_homU (\<iota> B (Rep_alpha B \<beta>)) (\<theta> x)) y'"
  by (simp add: H'_def)



subsection \<open>Construction\<close>

definition \<alpha>0 :: "'x \<Rightarrow> 'y shuffle" where
  "\<alpha>0 x = idS"


definition convert_\<delta> :: "'i::enum boundedness \<Rightarrow> ('q, 'x, 'y::enum, 'a, 'b) MSST \<Rightarrow> ('q \<times> ('x \<Rightarrow> ('i, 'y) bc_shuffle), 'a) trans" where
  "convert_\<delta> B msst =
     (\<lambda>((q1, \<beta>), a). (delta msst (q1, a), \<Delta>' B (\<beta>, eta msst (q1, a))))"

definition convert_\<eta> :: "'i::enum boundedness \<Rightarrow> ('q, 'x, 'y::enum, 'a, 'b) MSST \<Rightarrow>
                         ('q \<times> ('x \<Rightarrow> ('i, 'y) bc_shuffle), 'x \<times> ('y, 'i) index, 'a, 'b) updator" where
  "convert_\<eta> B msst = (\<lambda>((q, \<beta>), b). H' B (\<beta>, eta msst (q, b)))"

definition convert_final :: "'i::enum boundedness \<Rightarrow> ('q, 'x, 'y::enum, 'a, 'b) MSST \<Rightarrow>
   ('q \<times> ('x \<Rightarrow> ('i, 'y) bc_shuffle) \<Rightarrow> ('x \<times> ('y, 'i) index + 'b) list option)" where
  "convert_final B msst = (\<lambda>(q, \<beta>).
     (case final_update msst q of
        Some u \<Rightarrow> (case final_string msst q of
          Some v \<Rightarrow> Some (valuate (hat_hom (hat_homU (\<iota> B (Rep_alpha B \<beta>)) u) (hat_alpha inr_list v))) |
          None \<Rightarrow> None) |
        None \<Rightarrow> None))"

lemma convert_\<delta>_simp: "convert_\<delta> B msst ((q1, \<beta>), a) = (delta msst (q1, a), \<Delta>' B (\<beta>, eta msst (q1, a)))"
  by (simp add: convert_\<delta>_def)

lemma convert_\<eta>_simp: "convert_\<eta> B msst ((q1, \<beta>), a) = H' B (\<beta>, eta msst (q1, a))"
  by (simp add: convert_\<eta>_def)

definition convert_MSST :: "'i::enum boundedness \<Rightarrow> ('q, 'x, 'y::enum, 'a, 'b) MSST \<Rightarrow>
                            ('q \<times> ('x \<Rightarrow> ('i, 'y) bc_shuffle), 'x \<times> ('y, 'i) index, 'a, 'b) SST" where
  "convert_MSST B msst = \<lparr>
    initial = (initial msst, Abs_alpha B \<alpha>0),
    delta       = convert_\<delta> B msst,
    eta         = convert_\<eta> B msst,
    final       = convert_final B msst
  \<rparr>"


lemma convert_\<delta>_state:
  assumes "(q', \<beta>') = delta_hat (convert_MSST B msst) ((q, \<beta>), w)"
  shows "q' = delta_hat msst (q, w)"
proof -
  { fix qa
    have "fst (delta_hat (convert_MSST B msst) (qa, w)) = delta_hat msst (fst qa, w)"
    proof (induct w arbitrary: qa)
      case Nil
      then show ?case by simp
    next
      case (Cons a w)
      then show ?case 
        by (simp add: convert_MSST_def convert_\<delta>_def prod.case_eq_if)
    qed
  }
  then show ?thesis using assms
    unfolding convert_MSST_def convert_\<delta>_def by (metis (no_types, lifting) fst_conv)
qed

lemma reachable_convert:
  assumes "reachable (convert_MSST B msst) (q, \<beta>)"
  shows "reachable msst q"
proof -
  obtain w where w: "(q, \<beta>) = delta_hat (convert_MSST B msst) (initial (convert_MSST B msst), w)"
    using assms unfolding reachable_def by auto
  have "q = delta_hat msst (initial msst, w)"
    apply (rule convert_\<delta>_state)
    using w unfolding convert_MSST_def
    by simp
  then show ?thesis
    unfolding reachable_def by auto
qed

lemma [simp]:
  fixes B :: "'k::enum boundedness"
  shows "Rep_alpha B (Abs_alpha B \<alpha>0 :: 'x \<Rightarrow> ('k, 'y::enum) bc_shuffle) = \<alpha>0"
proof (rule Abs_alpha_inverse)
  show "boundedness B (length (Enum.enum :: 'k list))"
    unfolding boundedness_def by simp
next
  show "\<forall>x. bounded_shuffle (length (Enum.enum :: 'k list)) (\<alpha>0 x :: 'y shuffle)"
    unfolding \<alpha>0_def apply simp
    by (rule idS_bounded_enum)
qed

end
