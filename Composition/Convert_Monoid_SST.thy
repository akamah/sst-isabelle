(* Title:   Convert_Monoid_SST.thy
   Author:  Akama Hitoshi
*)

section \<open>Proof of convertion from a Monoid SST to a ordinary SST\<close>

theory Convert_Monoid_SST
  imports Main HOL.Sum_Type "../Core/Update" "../Core/SST" "../Core/Monoid_SST" "../Decomposition/Decompose_Update"
                         "../Type/Monoid_SST_Type" "Convert_Monoid_SST_Def" "Convert_Monoid_SST_Type_Misc"
begin

subsection \<open>Properties\<close>


lemma \<Delta>'_id: "\<Delta>' B (\<alpha>, idU) = \<alpha>"
  by (rule ext, simp add: \<Delta>'_def idU_def resolve_shuffle_def \<iota>_def synthesize_inverse_shuffle Rep_bc_shuffle_inverse)
 

lemma \<Delta>'_assoc:
  fixes B :: "'k::enum boundedness"
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  assumes assm_k_bounded: "boundedness B k"
  assumes assm_bounded_type: "bctype k msst \<gamma>"
  assumes assm_reachable: "reachable (convert_MSST B msst) (q, \<beta>)"
  shows  "\<Delta>' B (\<beta>, SST.eta_hat msst (q, w) \<bullet> \<psi>) = \<Delta>' B (\<Delta>' B (\<beta>, SST.eta_hat msst (q, w)), \<psi>)"
proof -
  let ?alpha = "Rep_alpha B \<beta>"
  let ?theta = "SST.eta_hat msst (q, w)"
  let ?inner = "(\<lambda>x. \<pi>\<^sub>1 (hat_homU (\<iota> B ?alpha) (?theta x)))"
  have \<Delta>'_assoc_string: "\<pi>\<^sub>1 (hat_homU (\<iota> B ?alpha) (hat_hom ?theta u))
       = \<pi>\<^sub>1 (hat_homU (\<iota> B (\<lambda>y. \<pi>\<^sub>1 (hat_homU (\<iota> B ?alpha) (?theta y)))) u)" for u
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
  have *: "\<forall>x. bounded_shuffle k (?inner x)"
    apply (rule allI)
    apply (rule resolve_bounded)
    apply (rule hat_homU_iota_bounded_copy[OF assms])
    done
  then show ?thesis
    by (intro ext, simp add: \<Delta>'_def compU_apply \<Delta>'_assoc_string Abs_alpha_inverse[OF assms(1) *])
qed


lemma convert_\<delta>_hat:
  fixes B :: "'k::enum boundedness"
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  assumes assm_k_bounded: "boundedness B k"
  assumes assm_bounded_type: "bctype k msst \<gamma>"
  assumes assm_reachable: "reachable (convert_MSST B msst) (q, \<beta>)"
  shows "hat1 (convert_\<delta> B msst) ((q, \<beta>), w)
       = (delta_hat msst (q, w), \<Delta>' B (\<beta>, eta_hat msst (q, w)))"
using assm_reachable proof (induct w arbitrary: q rule: rev_induct)
  case Nil
  then show ?case by (simp add: convert_\<delta>_simp \<Delta>'_id)
next
  case (snoc a w)
  then show ?case 
    by (simp add: eta_append convert_\<delta>_simp \<Delta>'_assoc[OF assm_k_bounded assm_bounded_type snoc.prems])
qed

lemma compU_valuate:
  fixes t :: "('y, 'z, 'b) update'"
  fixes \<theta> :: "('w, 'x, 'y + 'b) update'"
  shows "t \<bullet> (valuate o \<theta>) = valuate o (update2hom t \<star> \<theta>)"
proof (rule ext, simp add: compU_apply map_alpha_apply)
  show "hat_hom t (valuate u) = valuate (hat_alpha (update2hom t) u)" for u :: "('x + 'y + 'b) list"
    by (induct u rule: xa_induct, simp_all add: hat_hom_def)
qed


lemma update2hom_map_alpha:
  fixes t :: "('y, 'z, 'b) update'"
  fixes \<theta> :: "('w, 'x, 'b) update'"
  shows "update2hom t \<star> inr_list \<star> \<theta> = inr_list \<star> \<theta>"
proof (rule ext, simp add: map_alpha_def)
  show "hat_alpha (update2hom t) (hat_alpha inr_list w) = hat_alpha inr_list w" for w :: "('x + 'b) list"
    by (induct w rule: xa_induct, simp_all)
qed

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
    then show ?thesis by (simp add: map_alpha_distrib Cons update2hom_map_alpha)
  qed
qed  


lemma hat_homU_lem: "hat_homU (hat_homU \<phi> o \<theta>) m = hat_homU \<phi> (hat_hom \<theta> m)"
  by (induct m rule: xa_induct, simp_all add: hat_homU_append)


lemma valuate_update_map_alpha:
  fixes \<theta> :: "('y, 'b + 'c) update"
  shows "valuate (valuate (\<theta> x)) = valuate ((retain_right \<star> \<theta>) x)"
proof (simp add: map_alpha_apply)
  show "valuate (valuate u) = valuate (hat_alpha retain_right u)" for u :: "('y + 'b + 'c) list"
  proof (induct u rule: xa_induct)
    case (Alpha a xs)
    then show ?case by (cases a, simp_all)
  qed (simp_all)
qed

lemma retain_right_inr_list_eq_idS: "(retain_right \<odot> inr_list) = idS"
  by (rule ext, simp add: compS_apply idS_def)

lemma retain_right_embed: "retain_right \<odot> Convert_Monoid_SST_Def.embed x = empty_store"
  by (rule ext_prod, simp add: compS_apply)

lemma retain_right_hat_homU_iota_alpha0:
  "retain_right \<star> hat_homU (\<iota> B \<alpha>0) m = concatU (valuate m)"
proof (induct m rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case
    by (simp add: map_alpha_distrib \<iota>_def \<alpha>0_def map_alpha_synthesize retain_right_embed synthesize_idU)
next
  case (Alpha a xs)
  then show ?case
    by (simp add: map_alpha_distrib map_alpha_assoc retain_right_inr_list_eq_idS)
qed

lemma iota_alpha0_remove_aux:
  "valuate (valuate (hat_homU (\<iota> B \<alpha>0) m x')) 
 = valuate (concatU (valuate m) x')"
  by (simp add: valuate_update_map_alpha retain_right_hat_homU_iota_alpha0)

lemma iota_alpha0_remove:
  "valuate (valuate (hat_hom (hat_homU (\<iota> B \<alpha>0) m) (hat_alpha inr_list u))) 
 = valuate (hat_hom (concatU (valuate m)) u)"
  by (induct u rule: xa_induct, simp_all add: iota_alpha0_remove_aux)

lemma H'_embed: "H' B (\<beta>, \<theta>) \<bullet> Convert_Monoid_SST_Def.embed x = \<pi>\<^sub>2 B (hat_homU (\<iota> B (Rep_alpha B \<beta>)) (\<theta> x))"
  by (auto simp add: compU_apply H'_def)

(* SST.eta_hat msst (q, w) *)
lemma map_alpha_H'_iota_\<Delta>:
  fixes x :: "'x"
  fixes \<alpha> :: "'x \<Rightarrow> 'y::enum shuffle"
  fixes \<theta> :: "('x, ('y, 'b) update) update"
  assumes "boundedness B k"
  assumes "bctype k msst \<gamma>"
  assumes "reachable (convert_MSST B msst) (q, \<beta>)"
  shows "map_alpha (update2hom (H' B (\<beta>, SST.eta_hat msst (q, w)))) o \<iota> B (Rep_alpha B (\<Delta>' B (\<beta>, SST.eta_hat msst (q, w)))) 
       = hat_homU (\<iota> B (Rep_alpha B \<beta>)) o SST.eta_hat msst (q, w)"
  apply (rule ext)
  apply (simp add: \<iota>_def map_alpha_synthesize compU_apply hat_hom_def[symmetric] H'_embed \<Delta>'_def update2hom_compS_compU)
  apply (simp only: resolve_shuffle_hat_homU_inverse[OF assms])
  apply (rule resolve_inverse)
  apply (rule assms(1))
  apply (rule hat_homU_iota_bounded_copy)
  apply (rule assms)+
  done


lemma hat_homU_iota:
  assumes "boundedness B k"
  assumes "bctype k msst \<gamma>"
  assumes "reachable (convert_MSST B msst) (q, \<beta>)"
  shows "hat_homU (\<iota> B (Rep_alpha B \<beta>)) (hat_hom (SST.eta_hat msst (q, w)) u)
       = update2hom (H' B (\<beta>, SST.eta_hat msst (q, w))) \<star> hat_homU (\<iota> B (Rep_alpha B (\<Delta>' B (\<beta>, SST.eta_hat msst (q, w))))) u"
  by (simp add: hat_homU_map_alpha hat_homU_lem map_alpha_H'_iota_\<Delta>[OF assms])


lemma H'_assoc:
  fixes \<beta> :: "'x \<Rightarrow> ('k::enum, 'y::enum) bc_shuffle"
  assumes "boundedness B k"
  assumes "bctype k msst \<gamma>"
  assumes "reachable (convert_MSST B msst) (q, \<beta>)"
  shows "H' B (\<beta>, SST.eta_hat msst (q, w) \<bullet> \<psi>)
       = H' B (\<beta>, SST.eta_hat msst (q, w)) \<bullet> H' B (\<Delta>' B (\<beta>, SST.eta_hat msst (q, w)), \<psi>)"
proof -
  have "\<pi>\<^sub>2 B (hat_homU (\<iota> B (Rep_alpha B \<beta>)) (hat_hom (SST.eta_hat msst (q, w)) u)) (y, e)
       = (H' B (\<beta>, SST.eta_hat msst (q, w)) 
         \<bullet> \<pi>\<^sub>2 B (hat_homU (\<iota> B (Rep_alpha B (\<Delta>' B (\<beta>, SST.eta_hat msst (q, w))))) u)) (y, e)" for u y e
    by (simp add: hat_homU_iota[OF assms] map_alpha_resolve_store)
  then have "H' B (\<beta>, SST.eta_hat msst (q, w) \<bullet> \<psi>) (x, y, e) 
           = (H' B (\<beta>, SST.eta_hat msst (q, w)) \<bullet> H' B (\<Delta>' B (\<beta>, SST.eta_hat msst (q, w)), \<psi>)) (x, y, e)" for x y e
    by (simp add: compU_apply H'_simp2)
  then show ?thesis by auto
qed

lemma convert_\<eta>_hat_gt_0:
  fixes msst :: "('q, 'x, 'y::enum, 'a, 'b) MSST"
  fixes \<beta> :: "'x \<Rightarrow> ('k::enum, 'y::enum) bc_shuffle"
  assumes "boundedness B k"
  assumes "bctype k msst \<gamma>"
  assumes reach: "reachable (convert_MSST B msst) (q, \<beta>)"
  assumes len: "0 < length w"
  shows   "SST.hat2 (convert_\<delta> B msst) (convert_\<eta> B msst) ((q, \<beta>), w)
         = H' B (\<beta>, eta_hat msst (q, w))"
using reach len proof (induct w arbitrary: q \<beta>)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case proof (cases "length w")
    case 0 then show ?thesis by (simp add: eta_convert_MSST_simp convert_\<eta>_simp)
  next
    case (Suc nat) then show ?thesis proof -
      let ?qb' = "convert_\<delta> B msst ((q, \<beta>), a)"
      have l: "0 < length w" by (simp add: Suc)
      have r: "reachable (convert_MSST B msst) (fst ?qb', snd ?qb')"
        by (simp add: reachable_delta[OF Cons.prems(1)] delta_convert_MSST_simp[symmetric])
      have hat: "SST.eta msst (q, a) = SST.eta_hat msst (q, [a])" by (simp add:)
      show ?thesis
        apply (simp add: Cons.hyps[OF r l, simplified])
        apply (simp add: delta_convert_MSST_simp eta_convert_MSST_simp convert_\<eta>_simp convert_\<delta>_simp)
        apply (simp only: hat)
        apply (rule H'_assoc[symmetric, OF assms(1-2) Cons.prems(1)])
        done
    qed
  qed
qed


lemma list_all_isl_valuate:
  assumes "list_all isl bs"
  shows "valuate bs = []"
  using assms by (induct bs rule: xa_induct, simp_all)

lemma valuate_H'_Nil_var: "valuate (H' B (\<alpha>, idU) (x, y, k)) = []"
proof (simp add: H'_def idU_def \<iota>_def)
  let ?beta = "Rep_bc_shuffle (\<alpha> x)"
  let ?m = "\<pi>\<inverse> B (Rep_bc_shuffle (\<alpha> x), embed x)"
  have "\<forall>y k. list_all isl (embed x (y, k))"
    by simp
  then have "\<forall>y. list_all isl (valuate (?m y))"
    by (rule synthesize_preserve_prop_on_string)
  then have "list_all isl (\<pi>\<^sub>2 B ?m (y, k))"
    using resolve_store_preserve_prop_on_string by blast
  then show "valuate (\<pi>\<^sub>2 B ?m (y, k)) = []"
    by (rule list_all_isl_valuate)
qed

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

lemma convert_\<eta>_hat_valuate:
  assumes "boundedness B k"
  assumes "bctype k msst \<gamma>"
  assumes "reachable (convert_MSST B msst) (q, \<alpha>)"
  shows   "valuate o (SST.hat2 (convert_\<delta> B msst) (convert_\<eta> B msst) ((q, \<alpha>), w) \<bullet> \<phi>)
         = valuate o (H' B (\<alpha>, eta_hat msst (q, w)) \<bullet> \<phi>)"
proof (cases "w")
  case Nil
  show ?thesis by (rule ext, simp add: Nil valuate_H'_Nil compU_apply)
next
  case (Cons _ _)
  then have l: "0 < length w" by simp
  then show ?thesis by (simp add: convert_\<eta>_hat_gt_0[OF assms])
qed


lemma reach0: "reachable (convert_MSST B msst) (initial msst, Abs_alpha B \<alpha>0)"
  by (simp add: reachable_initial initial_convert_MSST_simp[symmetric])

theorem MSST_can_convert:
  assumes assm_k_bounded: "boundedness B k"
  assumes assm_bounded_type: "bctype k msst \<gamma>"
  shows "SST.run (convert_MSST B msst) w = Monoid_SST.run msst w"
proof (cases "final msst (hat1 (delta msst) (initial msst, w))")
  case None
  show ?thesis
    by (simp add: convert_MSST_def SST.run_def Monoid_SST.run_def convert_final_def convert_\<delta>_hat[OF assms reach0] None)    
next
  case Some1: (Some m)
  show ?thesis proof (cases "final_string msst (hat1 (delta msst) (initial msst, w))")
    case None
    then show ?thesis
      by (simp add: convert_MSST_def SST.run_def Monoid_SST.run_def convert_final_def convert_\<delta>_hat[OF assms reach0] Some1)
  next
    case Some2: (Some u)
    show ?thesis
      apply (simp add: SST.run_def Monoid_SST.run_def initial_convert_MSST_simp final_convert_MSST_simp)
      apply (simp add: convert_final_def convert_\<delta>_hat[OF assms reach0] Some1 Some2
                 initial_convert_MSST_simp delta_convert_MSST_simp eta_convert_MSST_simp convert_\<eta>_hat_valuate[OF assms reach0] del: comp_apply)
      apply (simp add: compU_valuate del: comp_apply)
      apply (simp add: map_alpha_distrib del: comp_apply)
      apply (simp add: hat_homU_map_alpha del: comp_apply)
      apply (simp add: update2hom_map_alpha del: comp_apply)
      apply (simp add: map_alpha_H'_iota_\<Delta>[OF assms reach0] del: comp_apply)
      apply (simp add: hat_homU_lem)
      apply (simp add: iota_alpha0_remove compU_apply map_alpha_apply)
      done
  qed
qed

hide_fact reach0

end
