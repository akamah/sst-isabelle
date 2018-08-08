theory Convert_Monoid_SST_Type_Misc
  imports Main 
          "../Core/Update" "../Core/SST" "../Core/Monoid_SST" "../Decomposition/Decompose_Update"
          "../Composition/Convert_Monoid_SST_Def"
          "../Type/Monoid_SST_Type"
begin


lemma condition_of_convert_MSST_state:
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  fixes \<gamma> :: "('q, 'x, 'y) msst_type"
  fixes B :: "'k::enum boundedness"
  assumes assm_is_type: "is_type msst \<gamma>"
  assumes assm_bc_type: "bounded_copy_type k msst \<gamma>"
  assumes assm_bounded: "boundedness B k"
  assumes assm_states:  "(q, \<alpha>) = delta_hat (convert_MSST B msst) (initial (convert_MSST B msst), w)"
  shows "\<alpha> x \<in> \<gamma> (q, x)"
using assm_states proof (induct w arbitrary: q \<alpha> x)
case Nil
  then show ?case
    using assm_is_type unfolding convert_MSST_def \<alpha>0_def is_type_def by simp
next
  case (Cons a w)
  then show ?case apply simp thm is_type_def
qed

end
