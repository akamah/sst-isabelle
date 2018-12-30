theory Bounded_Copy_SST_SST
  imports Main HOL.Finite_Set
          "../Core/Update" "../Composition/Compose_SST_SST" "../Single_Use/Single_Use"
begin


lemma count_list_H:
  "count_list (extract_variables (H tr to (f, \<theta>) (q, x))) (q0, x0)
 \<le> count_list (extract_variables (\<theta> x)) x0"
proof (simp add: H_def)
  show "count_list (extract_variables (Transducer.hat2 (delta2f f tr) (eta2f to) (q, u))) (q0, x0)
      \<le> count_list (extract_variables u) x0" for u
   by  (induct u arbitrary: q rule: xa_induct, simp_all add: Nat.le_SucI)
qed

lemma compose_reachable_SST_SST:
  assumes "reachable (compose_SST_SST sst1 sst2) (q1, f)"
  shows "reachable sst1 q1"
  unfolding reachable_def
proof -
  obtain w where *: "(q1, f) = delta_hat (compose_SST_SST sst1 sst2)
                                (initial (compose_SST_SST sst1 sst2), w)"
    using assms unfolding reachable_def by auto
  show "\<exists>w. q1 = delta_hat sst1 (initial sst1, w)" proof 
    show "q1 = delta_hat sst1 (initial sst1, w)"
      using * by (simp add: compose_\<delta>_hat compose_SST_SST_def)
  qed
qed


theorem compose_SST_SST_bounded:
  fixes sst1 :: "('q1::finite, 'x1::finite, 'a, 'b) SST"
  fixes sst2 :: "('q2::finite, 'x2::finite, 'b, 'c) SST"
  assumes "bounded_copy_SST k sst1"
  shows "bounded_copy_SST (card (UNIV::'q2 set) * k) (compose_SST_SST sst1 sst2)"
proof (simp add: bounded_copy_SST_def, intro allI, rule impI)
  fix w qs f
  let ?tr = "delta sst2" and ?to = "SST.eta sst2"
  let ?xi = "SST.eta_hat sst1 (qs, w)"
  assume r0: "reachable (compose_SST_SST sst1 sst2) (qs, f)"
  have reach: "reachable sst1 qs" by (rule compose_reachable_SST_SST, rule r0)
  show "bounded (card (UNIV::'q2 set) * k) (SST.eta_hat (compose_SST_SST sst1 sst2) ((qs, f), w))"
    unfolding compose_SST_SST_def bounded_def count_var_def
  proof (simp add: compose_\<eta>_hat, intro allI)
    fix q0 x0
    have "(\<Sum>y\<in>(UNIV::('q2\<times>'x1)set). count_list (extract_variables (H ?tr ?to (f, ?xi) y)) (q0, x0))
        = (\<Sum>q\<in>(UNIV::'q2 set). \<Sum>x\<in>(UNIV::'x1 set). count_list (extract_variables (H ?tr ?to (f, ?xi) (q, x))) (q0, x0))"
      by (simp add: sum.Sigma)
    also have "... \<le> (\<Sum>q\<in>(UNIV::'q2 set). \<Sum>x\<in>(UNIV::'x1 set).  count_list (extract_variables (?xi x)) x0)"
      by (intro sum_mono, rule count_list_H)
    also have "... = card (UNIV::'q2 set) * (\<Sum>x\<in>(UNIV::'x1 set). count_list (extract_variables (?xi x)) x0)"
      by (simp)
    also have "... \<le> card (UNIV::'q2 set) * k"
      using assms reach unfolding bounded_copy_SST_def bounded_def count_var_def
      by (simp add: reach)
    finally show "(\<Sum>y\<in>(UNIV::('q2\<times>'x1)set). count_list (extract_variables (H ?tr ?to (f, ?xi) y)) (q0, x0)) 
                \<le> card (UNIV::'q2 set) * k" .
  qed
qed

end


