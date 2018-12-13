theory Bounded_Copy_SST_Transducer
  imports Main HOL.Finite_Set
          "../Core/Update" "../Composition/Compose_SST_Transducer" "../Single_Use/Single_Use"
begin


lemma count_list_H:
  "count_list (extract_variables (Transducer.hat2 (delta2f f tr) (eta2f to) (q, u))) (q0, x0)
 \<le> count_list (extract_variables u) x0"
  by (induct u arbitrary: q rule: xa_induct, simp_all add: Nat.le_SucI)

lemma compose_reachable:
  assumes "reachable (compose_SST_Transducer sst td) (q1, f)"
  shows "reachable sst q1"
  unfolding reachable_def
proof -
  obtain w where *: "(q1, f) = delta_hat (compose_SST_Transducer sst td)
                                (initial (compose_SST_Transducer sst td), w)"
    using assms unfolding reachable_def by auto
  show "\<exists>w. q1 = delta_hat sst (initial sst, w)" proof 
    show "q1 = delta_hat sst (initial sst, w)"
      using * by (simp add: compose_\<delta>_hat compose_SST_Transducer_def)
  qed
qed


theorem compose_SST_Transducer_bounded:
  fixes sst :: "('q1::finite, 'x::finite, 'a, 'b) SST"
  fixes td  :: "('q2::finite, 'b, 'c) transducer"
  assumes "bounded_copy_SST k sst"
  shows "bounded_copy_SST (card (UNIV::'q2 set) * k) (compose_SST_Transducer sst td)"
proof (simp add: bounded_copy_SST_def, intro allI, rule impI)
  fix w qs f
  let ?tr = "delta td" and ?to = "transducer.eta td"
  let ?xi = "SST.eta_hat sst (qs, w)"
  assume r0: "reachable (compose_SST_Transducer sst td) (qs, f)"
  have reach: "reachable sst qs" by (rule compose_reachable, rule r0)
  show "bounded (card (UNIV::'q2 set) * k) (SST.eta_hat (compose_SST_Transducer sst td) ((qs, f), w))"
    unfolding compose_SST_Transducer_def bounded_def count_var_def
  proof (simp add: compose_\<eta>_hat, intro allI)
    fix q0 x0
    have "(\<Sum>y\<in>(UNIV::('q2\<times>'x)set). count_list (extract_variables (H ?tr ?to (f, ?xi) y)) (q0, x0))
        = (\<Sum>q\<in>(UNIV::'q2 set). \<Sum>x\<in>(UNIV::'x set). count_list (extract_variables (H ?tr ?to (f, ?xi) (q, x))) (q0, x0))"
      by (simp add: sum.Sigma)
    also have "... = (\<Sum>q\<in>(UNIV::'q2 set). \<Sum>x\<in>(UNIV::'x set). 
                         count_list (extract_variables (Transducer.hat2 (delta2f f ?tr) (eta2f ?to) (q, ?xi x))) (q0, x0))"
      by (simp add: H_def)
    also have "... \<le> (\<Sum>q\<in>(UNIV::'q2 set). \<Sum>x\<in>(UNIV::'x set).
                         count_list (extract_variables (?xi x)) x0)" by (intro sum_mono, rule count_list_H)
    also have "... = card (UNIV::'q2 set) * (\<Sum>x\<in>(UNIV::'x set). count_list (extract_variables (?xi x)) x0)" by (simp)
    also have "... \<le> card (UNIV::'q2 set) * k"
      using assms reach unfolding bounded_copy_SST_def bounded_def count_var_def
      by (simp add: reach)
    finally show "(\<Sum>y\<in>(UNIV::('q2\<times>'x)set). count_list (extract_variables (H ?tr ?to (f, ?xi) y)) (q0, x0))
                \<le> card (UNIV::'q2 set) * k" .
  qed
qed

end


