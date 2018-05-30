theory Bounded_Copy_SST_Transducer
  imports Main Update Compose_SST_Transducer SingleUse Finite_Set
begin

definition bounded_copy_SST :: "[ nat, ('q::finite, 'x::finite, 'a, 'b) SST ] \<Rightarrow> bool" where
  "bounded_copy_SST k sst \<equiv> (\<forall>w. bounded k (SST.eta_hat sst (SST.initial sst, w)))"


(*
lemma finite_set_choice: "finite A \<Longrightarrow> \<forall>x\<in>A. \<exists>y. P x y \<Longrightarrow> \<exists>f. \<forall>x\<in>A. P x (f x)"
proof (induct A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert a A)
  then obtain f b where f: "\<forall>x\<in>A. P x (f x)" and ab: "P a b"
    by auto
  show ?case (is "\<exists>f. ?P f")
  proof
    show "?P (\<lambda>x. if x = a then b else f x)"
      using f ab by auto
  qed
qed
*)

lemma product_type_sum_aux: 
  "finite B \<Longrightarrow> finite F \<Longrightarrow> sum f (insert x F \<times> B) = (\<Sum>i\<in>insert x F. \<Sum>j\<in>B. f (i, j))"
proof (induct B rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case apply (simp add: sum.distrib) sorry
qed


lemma product_type_sum:
  "finite A \<Longrightarrow> finite B \<Longrightarrow> (\<Sum>y\<in>A\<times>B. f y) = (\<Sum>i\<in>A. \<Sum>j\<in>B. f (i, j))"
proof (induct A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case by (simp add: product_type_sum_aux)
qed

lemma count_list_Inr: "count_list (map Inr w) (Inl x) = 0"
  by (induct w, simp_all)

lemma count_list_H:
  "count_list (Transducer.hat2 (delta2f f tr) (eta2f to) (q, u)) (Inl (q0::('q::finite), x0::('x::finite)))
 \<le> count_list u (Inl x0)"
proof (induct u arbitrary: q rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case by (auto simp add: Nat.le_SucI)
next
  case (Alpha a xs)
  then show ?case by (auto simp add: count_list_Inr)
qed
declare[[show_types]]
theorem compose_SST_Transducer_bounded:
  fixes sst :: "('q1::finite, 'x::finite, 'a, 'b) SST"
  fixes td  :: "('q2::finite, 'b, 'c) transducer"
  assumes "bounded_copy_SST k sst"
  shows "bounded_copy_SST (card (UNIV::'q2 set) * k) (compose_SST_Transducer sst td)"
  unfolding bounded_copy_SST_def bounded_def compose_SST_Transducer_def count_var_def
proof (simp add: compose_\<eta>_hat, intro allI)
  fix w q0 x0
  let ?tr = "transducer.delta td" and ?to = "transducer.eta td"
  let ?f0 = "(\<lambda>(q2, x1). q2)"
  let ?xi = "SST.eta_hat sst (SST.initial sst, w)"
  have "(\<Sum>y\<in>(UNIV::('q2\<times>'x)set). count_list (H ?tr ?to (?f0, ?xi) y) (Inl (q0, x0)))
      = (\<Sum>q\<in>(UNIV::'q2 set). \<Sum>x\<in>(UNIV::'x set). count_list (H ?tr ?to (?f0, ?xi) (q, x)) (Inl (q0, x0)))"
    apply (simp add: UNIV_Times_UNIV[symmetric] del: UNIV_Times_UNIV)
    apply (rule product_type_sum, simp_all)
    done
  also have "... = (\<Sum>q\<in>(UNIV::'q2 set). \<Sum>x\<in>(UNIV::'x set). 
                       count_list (Transducer.hat2 (delta2f ?f0 ?tr) (eta2f ?to) (q, ?xi x)) (Inl (q0, x0)))"
    by (simp add: H_def)
  also have "... \<le> (\<Sum>q\<in>(UNIV::'q2 set). \<Sum>x\<in>(UNIV::'x set).
                       count_list (?xi x) (Inl x0))" by (intro sum_mono, rule count_list_H)
  also have "... = card (UNIV::'q2 set) * (\<Sum>x\<in>(UNIV::'x set). count_list (?xi x) (Inl x0))" by (simp)
  also have "... \<le> card (UNIV::'q2 set) * k" proof -
    have "(\<Sum>x\<in>(UNIV::'x set). count_list (?xi x) (Inl x0)) \<le> k"
      using assms by (simp add: assms bounded_copy_SST_def bounded_def count_var_def)
    then show ?thesis by simp
  qed
  finally show "(\<Sum>y\<in>(UNIV::('q2\<times>'x)set). count_list (H ?tr ?to (?f0, ?xi) y) (Inl (q0, x0))) 
              \<le> card (UNIV::'q2 set) * k" .
qed


end


