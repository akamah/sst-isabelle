theory Bounded_Copy_SST_Transducer
  imports Main Update Compose_SST_Transducer SingleUse Finite_Set Bounded_Copy
begin


lemma count_list_Inr: "count_list (map Inr w) (Inl x) = 0"
  by (induct w, simp_all)

lemma count_list_H:
  "count_list (Transducer.hat2 (delta2f f tr) (eta2f to) (q, u)) (Inl (q0, x0))
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

theorem compose_SST_Transducer_bounded:
  fixes sst :: "('q1::finite, 'x::finite, 'a, 'b) SST"
  fixes td  :: "('q2::finite, 'b, 'c) transducer"
  assumes "bounded_copy_SST k sst"
  shows "bounded_copy_SST (card (UNIV::'q2 set) * k) (compose_SST_Transducer sst td)"
  unfolding bounded_copy_SST_def bounded_def compose_SST_Transducer_def count_var_def
proof (simp add: compose_\<eta>_hat, intro allI)
  fix w qs f q0 x0
  let ?tr = "transducer.delta td" and ?to = "transducer.eta td"
  let ?xi = "SST.eta_hat sst (qs, w)"
  have "(\<Sum>y\<in>(UNIV::('q2\<times>'x)set). count_list (H ?tr ?to (f, ?xi) y) (Inl (q0, x0)))
      = (\<Sum>q\<in>(UNIV::'q2 set). \<Sum>x\<in>(UNIV::'x set). count_list (H ?tr ?to (f, ?xi) (q, x)) (Inl (q0, x0)))"
    by (simp add: sum.Sigma)
  also have "... = (\<Sum>q\<in>(UNIV::'q2 set). \<Sum>x\<in>(UNIV::'x set). 
                       count_list (Transducer.hat2 (delta2f f ?tr) (eta2f ?to) (q, ?xi x)) (Inl (q0, x0)))"
    by (simp add: H_def)
  also have "... \<le> (\<Sum>q\<in>(UNIV::'q2 set). \<Sum>x\<in>(UNIV::'x set).
                       count_list (?xi x) (Inl x0))" by (intro sum_mono, rule count_list_H)
  also have "... = card (UNIV::'q2 set) * (\<Sum>x\<in>(UNIV::'x set). count_list (?xi x) (Inl x0))" by (simp)
  also have "... \<le> card (UNIV::'q2 set) * k"
    using assms 
    unfolding bounded_copy_SST_def bounded_def count_var_def
    by (simp)
  finally show "(\<Sum>y\<in>(UNIV::('q2\<times>'x)set). count_list (H ?tr ?to (f, ?xi) y) (Inl (q0, x0))) 
              \<le> card (UNIV::'q2 set) * k" .
qed

end


