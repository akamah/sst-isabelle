theory Compose_SST_SST_Type 
  imports "../Composition/Compose_SST_SST" "../Decomposition/Decompose_Update" Monoid_SST_Type
begin


definition all_shuffles where
  "all_shuffles sst2 q2 q2' =
    {m1. \<exists>w. delta_hat sst2 (q2, w) = q2' \<and>
           m1 = resolve_shuffle (SST.eta_hat sst2 (q2, w))}"

lemma all_shuffles_first:
  "resolve_shuffle (SST.eta sst2 (q2, a))
 \<in> all_shuffles sst2 q2 (delta sst2 (q2, a))"
  unfolding all_shuffles_def
  apply auto
  apply (rule exI[of _ "[a]"])
  apply (simp_all add: comp_right_neutral)
  done
  

lemma all_shuffles_mult:
  "mult_shuffles (all_shuffles sst2 q0 q1) (all_shuffles sst2 q1 q2)
 \<subseteq> all_shuffles sst2 q0 q2"
  unfolding mult_shuffles_def all_shuffles_def
proof (auto)
  fix u v
  assume "q1 = delta_hat sst2 (q0, u)"
  assume "q2 = delta_hat sst2 (delta_hat sst2 (q0, u), v)"
  show "\<exists>wb. delta_hat sst2 (q0, wb) = delta_hat sst2 (delta_hat sst2 (q0, u), v) \<and>
                 concat \<circ> map (resolve_shuffle (SST.eta_hat sst2 (q0, u))) \<circ>
                 resolve_shuffle (SST.eta_hat sst2 (delta_hat sst2 (q0, u), v)) =
                 resolve_shuffle (SST.eta_hat sst2 (q0, wb))"
    by (rule exI[where x="u@v"], auto simp add: eta_append resolve_shuffle_distrib)
qed

fun compose_\<gamma> ::
  "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'x2, 'b, 'c) SST \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'x2) msst_type" where
   "compose_\<gamma> sst1 sst2 ((_, f), (q2, x)) =
      all_shuffles sst2 q2 (f (q2, x))"


lemma compose_\<gamma>_ex:
  assumes "m \<in> compose_\<gamma> sst1 sst2 ((q1, f), (q2, x))"
  shows "\<exists>w. delta_hat sst2 (q2, w) = f (q2, x) \<and>
             m = resolve_shuffle (SST.eta_hat sst2 (q2, w))"
  using assms by (simp add: all_shuffles_def)


lemma idS_in_all_shuffles: 
  "idS \<in> all_shuffles sst q2 q2"
  unfolding all_shuffles_def
  apply (simp)
  apply (rule exI[of _ "[]"])
  apply (simp add: resolve_idU_idS)
  done


lemma compose_\<gamma>_subset:
  "type_hom (compose_\<gamma> sst1 sst2)
     ((q1, f), Transducer.hat2 (delta2f f (delta sst2)) (eta2f (SST.eta sst2)) (q2, u))
 \<subseteq> all_shuffles sst2 q2 (hat1 (delta2f f (delta sst2)) (q2, u))"
proof (induct u arbitrary: q2 rule: xa_induct)
  case Nil
  then show ?case by (simp add: idS_in_all_shuffles)
next
  case (Var x xs)
  then show ?case proof (simp_all)
    have "mult_shuffles (all_shuffles sst2 q2 (f (q2, x)))
     (type_hom (compose_\<gamma> sst1 sst2)
       ((q1, f), Transducer.hat2 (delta2f f (delta sst2)) (eta2f (SST.eta sst2)) (f (q2, x), xs)))
    \<subseteq> mult_shuffles (all_shuffles sst2 q2 (f (q2, x)))
     (all_shuffles sst2 (f (q2, x))
       (hat1 (delta2f f (delta sst2)) (f (q2, x), xs)))"
      apply (rule mult_shuffles_subset)
      apply (simp_all add: Var)
      done
    also have "...  \<subseteq> all_shuffles sst2 q2 (hat1 (delta2f f (delta sst2)) (f (q2, x), xs))"
      by (simp add: all_shuffles_mult)
    finally show "mult_shuffles (all_shuffles sst2 q2 (f (q2, x)))
     (type_hom (compose_\<gamma> sst1 sst2)
       ((q1, f), Transducer.hat2 (delta2f f (delta sst2)) (eta2f (SST.eta sst2)) (f (q2, x), xs)))
    \<subseteq> all_shuffles sst2 q2 (hat1 (delta2f f (delta sst2)) (f (q2, x), xs))" .
  qed
next
  case (Alpha a xs)
  then show ?case proof (simp_all)
    have "mult_shuffles {resolve_shuffle (SST.eta sst2 (q2, a))}
     (type_hom (compose_\<gamma> sst1 sst2)
       ((q1, f),
        Transducer.hat2 (delta2f f (delta sst2)) (eta2f (SST.eta sst2))
         (delta sst2 (q2, a), xs)))
    \<subseteq> mult_shuffles {resolve_shuffle (SST.eta sst2 (q2, a))}
       (all_shuffles sst2 (delta sst2 (q2, a))
         (hat1 (delta2f f (delta sst2)) (delta sst2 (q2, a), xs)))"
      by (rule mult_shuffles_subset, simp_all add: Alpha)
    also have "... 
    \<subseteq> mult_shuffles (all_shuffles sst2 q2 (delta sst2 (q2, a)))
       (all_shuffles sst2 (delta sst2 (q2, a))
         (hat1 (delta2f f (delta sst2)) (delta sst2 (q2, a), xs)))"
      by (rule mult_shuffles_subset, simp_all add: all_shuffles_first)
    also have "...  \<subseteq> all_shuffles sst2 q2 
                   (hat1 (delta2f f (delta sst2)) (delta sst2 (q2, a), xs))"
      by (simp add: all_shuffles_mult)
    finally show "mult_shuffles {resolve_shuffle (SST.eta sst2 (q2, a))}
     (type_hom (compose_\<gamma> sst1 sst2)
       ((q1, f),
        Transducer.hat2 (delta2f f (delta sst2)) (eta2f (SST.eta sst2))
         (delta sst2 (q2, a), xs)))
   \<subseteq> all_shuffles sst2 q2 
                   (hat1 (delta2f f (delta sst2)) (delta sst2 (q2, a), xs))" .
 qed
qed


lemma compose_typable:
  "is_type (compose_SST_SST sst1 sst2) (compose_\<gamma> sst1 sst2)"
  unfolding is_type_def
proof
  show "(\<forall>x. idS \<in> compose_\<gamma> sst1 sst2 (initial (compose_SST_SST sst1 sst2), x))"
    unfolding compose_SST_SST_def
    apply (simp add: all_shuffles_def)
    apply (metis hat1.simps(1) SST.hat2.simps(1) resolve_idU_idS)
    done
next
  show "\<forall>x q a. type_hom (compose_\<gamma> sst1 sst2) (q, SST.eta (compose_SST_SST sst1 sst2) (q, a) x)
                \<subseteq> compose_\<gamma> sst1 sst2 (delta (compose_SST_SST sst1 sst2) (q, a), x)"
    apply (simp add: compose_SST_SST_def compose_\<delta>_def \<Delta>_def compose_\<eta>_def H_def)
    apply (simp add: compose_\<gamma>_subset)
    done
qed

lemma eta2f_length:
  "length (Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (q, w)) = length w"
  by (induct w arbitrary: q rule: xa_induct, simp_all)

thm append_eq_append_conv

lemma eta2f_append_ex:
  assumes "u0 @ u1 = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) 
                                     (q2, v)"
  shows "\<exists>v1 v2. v = v1 @ v2 \<and>
                 u0 = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (q2, v1) \<and>
                 u1 = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (hat1 (delta2f f (delta sst2)) (q2, v1), v2)"
proof (intro exI)
  let ?v1 = "take (length u0) v"
  let ?v2 = "drop (length u0) v"
  have v: "v = ?v1 @ ?v2" by simp
  have len: "length (u0 @ u1) = length (Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) 
                                     (q2, v))"
    using assms by (simp only: eta2f_length)
  have "u0 @ u1 = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) 
                                     (q2, ?v1 @ ?v2)"
    using assms v by simp
  then have "u0 @ u1 = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (q2, ?v1)
                @ Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (hat1 (delta2f f (delta sst2)) (q2, ?v1), ?v2)"
    by (simp only: Transducer.eta_append)
  moreover have "length u0 = length (Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (q2, ?v1))"
    using len by (simp add: eta2f_length)
  moreover have "length u1 = length (Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (hat1 (delta2f f (delta sst2)) (q2, ?v1), ?v2))"
    using len by (simp add: eta2f_length)
  ultimately show "v = ?v1 @ ?v2 \<and>
                  u0 = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (q2, ?v1) \<and>
                  u1 = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (hat1 (delta2f f (delta sst2)) (q2, ?v1), ?v2)"
    by simp
qed

lemma tail_substring_ex:
  fixes sst1 :: "('q1, 'x, 'a, 'b) SST"
  fixes sst2 :: "('q2, 'y, 'b, 'c) SST"
  assumes "u \<in> tails (SST.eta_hat (compose_SST_SST sst1 sst2) ((q1, f), w) (q2, x))"
  shows "\<exists>v1 v2. SST.eta_hat sst1 (q1, w) x = v1 @ v2 \<and>
                 u = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) 
                               (hat1 (delta2f f (delta sst2)) (q2, v1), v2)"
proof -
  obtain u0 where "u0 @ u = eta_hat (compose_SST_SST sst1 sst2) ((q1, f), w) (q2, x)"
    using assms unfolding tails_def by auto
  then have u0: "u0 @ u = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (q2, SST.eta_hat sst1 (q1, w) x)"
    by (simp add: compose_\<eta>_hat H_def Transducer.eta_append assms compose_SST_SST_def)
  obtain v1 v2 where "v1 @ v2 = SST.eta_hat sst1 (q1, w) x \<and>
                       u0 = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (q2, v1) \<and>
                       u = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2))
                                                           (hat1 (delta2f f (delta sst2)) (q2, v1), v2)"
    using eta2f_append_ex[OF u0] by auto
  then have "SST.eta_hat sst1 (q1, w) x = v1 @ v2 \<and>
                 u = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) 
                               (hat1 (delta2f f (delta sst2)) (q2, v1), v2)"
    by simp
  then show ?thesis by auto
qed


theorem compose_\<gamma>_bounded:
  fixes sst2 :: "('q2::finite, 'x2::finite, 'b, 'c) SST"
  assumes "bounded_copy_SST k sst2"
  assumes "trim sst2"
  shows "bounded_copy_type k (compose_SST_SST sst1 sst2) (compose_\<gamma> sst1 sst2)"
proof (auto simp add: bounded_copy_type_def all_shuffles_def)
  fix q2 w
  have q2_reach: "reachable sst2 q2"
    using assms(2) unfolding trim_def by simp
  have "bounded k (SST.eta_hat sst2 (q2, w))"
    by (rule bounded_copy_SST_simp, simp_all add: assms q2_reach)
  then show "bounded_shuffle k (resolve_shuffle (SST.eta_hat sst2 (q2, w)))"
    by (rule resolve_bounded)
next
  fix q1 f q2 a x u m 
  assume "reachable (compose_SST_SST sst1 sst2) (q1, f)"
  let ?eta = "SST.eta (compose_SST_SST sst1 sst2) ((q1, f), a) (q2, x)"
  assume u: "u \<in> tails ?eta"
  assume m: "m \<in> type_hom (compose_\<gamma> sst1 sst2) ((q1, f), u)"
  obtain v where "?eta = v @ u" using u tails_def by auto
  

  have q2_reach: "reachable sst2 q2"
    using assms(2) unfolding trim_def by simp
  have "bounded_shuffle k m"
    sorry
  
qed

end













