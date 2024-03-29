theory Compose_SST_SST_Type 
  imports "../Composition/Compose_SST_SST" "../Decomposition/Decompose_Update" Monoid_SST_Type
begin


definition all_shuffles where
  "all_shuffles sst2 q2 q2' =
    {m1. \<exists>w. delta_hat sst2 (q2, w) = q2' \<and>
           m1 = \<pi>\<^sub>1 (SST.eta_hat sst2 (q2, w))}"

lemma all_shuffles_member:
  "\<pi>\<^sub>1 (SST.eta_hat sst2 (q2, w))
 \<in> all_shuffles sst2 q2 (delta_hat sst2 (q2, w))"
  unfolding all_shuffles_def by auto

lemma all_shuffles_first:
  "\<pi>\<^sub>1 (SST.eta sst2 (q2, a))
 \<in> all_shuffles sst2 q2 (delta sst2 (q2, a))"
  using all_shuffles_member[of sst2 q2 "[a]"]
  by simp

lemma all_shuffles_mult:
  "all_shuffles sst2 q0 q1 \<otimes> all_shuffles sst2 q1 q2
 \<subseteq> all_shuffles sst2 q0 q2"
  unfolding all_shuffles_def[of sst2 q0 q1] all_shuffles_def[of sst2 q1 q2] mult_shuffles_def
  by (rule subsetI,
      auto simp add: resolve_shuffle_distrib[symmetric] eta_append[symmetric]
                     all_shuffles_member delta_append[symmetric] simp del: delta_append)

fun compose_\<gamma> ::
  "('q1, 'x1, 'a, 'b) SST \<Rightarrow> ('q2, 'x2, 'b, 'c) SST \<Rightarrow>
   ('q1 \<times> ('q2 \<times> 'x1 \<Rightarrow> 'q2), 'q2 \<times> 'x1, 'x2) msst_type" where
   "compose_\<gamma> sst1 sst2 ((_, f), (q2, x)) =
      all_shuffles sst2 q2 (f (q2, x))"


lemma compose_\<gamma>_ex:
  assumes "m \<in> compose_\<gamma> sst1 sst2 ((q1, f), (q2, x))"
  shows "\<exists>w. delta_hat sst2 (q2, w) = f (q2, x) \<and>
             m = \<pi>\<^sub>1 (SST.eta_hat sst2 (q2, w))"
  using assms by (simp add: all_shuffles_def)

lemma idS_in_all_shuffles: 
  "idS \<in> all_shuffles sst q2 q2"
  using all_shuffles_member[of sst q2 "[]"]
  by (simp add: resolve_idU_idS)


lemma compose_\<gamma>_subset_inner:
  "type_hom (compose_\<gamma> sst1 sst2)
     ((q1, f), Transducer.hat2 (delta2f f (delta sst2)) (eta2f (SST.eta sst2)) (q2, u))
 \<subseteq> all_shuffles sst2 q2 (hat1 (delta2f f (delta sst2)) (q2, u))"
proof (induct u rule: xa_rev_induct)
  case Nil
  then show ?case by (simp add: idS_in_all_shuffles)
next
  case (Var x xs)
  show ?case
    apply (simp add: Transducer.eta_append)
    apply (rule subset_trans)
     apply (rule mult_shuffles_subset)
      apply (rule Var)
    apply (rule subset_refl)
     apply (rule all_shuffles_mult)
    done
next
  case (Alpha a xs)
  show ?case
    apply (simp add: Transducer.eta_append)
    apply (rule subset_trans)
     apply (rule mult_shuffles_subset)
     apply (rule Alpha)
      apply simp
      apply (rule all_shuffles_first)
    apply (rule all_shuffles_mult)
    done
qed

lemma compose_\<gamma>_subset:
  "type_hom (compose_\<gamma> sst1 sst2)
     ((q1, f), H (delta sst2) (eta sst2) (f, \<theta>) (q2, x))
 \<subseteq> all_shuffles sst2 q2 (\<Delta> (delta sst2) (f, \<theta>) (q2, x))"
  by (simp add: \<Delta>_def H_def compose_\<gamma>_subset_inner)


lemma eta2f_length:
  "length (Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (q, w)) = length w"
  by (induct w arbitrary: q rule: xa_induct, simp_all)

lemma eta2f_append_ex:
  assumes "u0 @ u1 = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (q2, v)"
  shows "\<exists>v1 v2. v = v1 @ v2 \<and>
                 u0 = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (q2, v1) \<and>
                 u1 = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (hat1 (delta2f f (delta sst2)) (q2, v1), v2)"
proof (intro exI)
  let ?v1 = "take (length u0) v"
  let ?v2 = "drop (length u0) v"
  have len: "length (u0 @ u1) = length (Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (q2, v))"
    using assms by (simp only: eta2f_length)
  have "u0 @ u1 = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (q2, ?v1 @ ?v2)"
    using assms by simp
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


lemma type_hom_eta2f_hat_ex_string:
  fixes sst1 :: "('q1, 'x, 'a, 'b) SST"
  fixes sst2 :: "('q2, 'y, 'b, 'c) SST"
  shows "\<forall>m \<in> type_hom (compose_\<gamma> sst1 sst2) ((q1, f), Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) (q2, v)).
         \<exists>w. delta_hat sst2 (q2, w) = hat1 (delta2f f (delta sst2)) (q2, v) \<and>
             \<pi>\<^sub>1 (SST.eta_hat sst2 (q2, w)) = m"
proof (induct v rule: xa_rev_induct)
  case Nil
  then show ?case by (simp, rule exI[where x="[]"], simp add: resolve_idU_idS)
next
  case (Var x xs)
  show ?case proof (simp add: Transducer.eta_append, rule ballI)
    let ?set1 = "type_hom (compose_\<gamma> sst1 sst2)
                  ((q1, f), Transducer.hat2 (delta2f f (delta sst2)) (eta2f (SST.eta sst2)) (q2, xs))"
    let ?q = "hat1 (delta2f f (delta sst2)) (q2, xs)"
    let ?q' = "(f (?q, x))"
    fix m
    assume "m \<in> mult_shuffles ?set1 (all_shuffles sst2 ?q ?q')"
    then obtain m1 m2 :: "'y shuffle" 
      where m: "m = m1 \<odot> m2 \<and>
             m1 \<in> ?set1 \<and>
             m2 \<in> (all_shuffles sst2 ?q ?q')"
      by (auto simp add: mult_shuffles_def)
    obtain w1 where w1: "delta_hat sst2 (q2, w1) = hat1 (delta2f f (delta sst2)) (q2, xs) \<and>
                         m1 = \<pi>\<^sub>1 (SST.eta_hat sst2 (q2, w1))"
      using m Var by auto
    obtain w2 where w2: "delta_hat sst2 (?q, w2) = ?q' \<and> m2 = \<pi>\<^sub>1 (SST.eta_hat sst2 (?q, w2))"
      using m unfolding all_shuffles_def by auto
    have "delta_hat sst2 (q2, w1 @ w2) = f (hat1 (delta2f f (delta sst2)) (q2, xs), x)"
      by (simp add: w1 w2)
    moreover have "\<pi>\<^sub>1 (SST.eta_hat sst2 (q2, w1 @ w2)) = m"
      by (simp add: SST.eta_append resolve_shuffle_distrib m w1 w2)
    ultimately show "\<exists>w. delta_hat sst2 (q2, w) = f (hat1 (delta2f f (delta sst2)) (q2, xs), x) \<and>
                         \<pi>\<^sub>1 (SST.eta_hat sst2 (q2, w)) = m"
      by (auto simp del: delta_append)
  qed
next
  case (Alpha a xs)
  show ?case proof (simp add: Transducer.eta_append, rule ballI)
    let ?q = "hat1 (delta2f f (delta sst2)) (q2, xs)"
    let ?q' = "delta sst2 (?q, a)"
    let ?set1 = "type_hom (compose_\<gamma> sst1 sst2)
                  ((q1, f), Transducer.hat2 (delta2f f (delta sst2)) (eta2f (SST.eta sst2)) (q2, xs))"
    let ?set2 = "{\<pi>\<^sub>1 (SST.eta sst2 (?q, a))}"
    fix m
    assume "m \<in> mult_shuffles ?set1 ?set2"
    then obtain m1 m2 :: "'y shuffle" 
      where m: "m = m1 \<odot> m2 \<and>
             m1 \<in> ?set1 \<and>
             m2 \<in> ?set2"
      by (auto simp add: mult_shuffles_def)
    obtain w1 where w1: "delta_hat sst2 (q2, w1) = hat1 (delta2f f (delta sst2)) (q2, xs) \<and>
                         m1 = \<pi>\<^sub>1 (SST.eta_hat sst2 (q2, w1))"
      using m Alpha by auto
    have w2: "delta_hat sst2 (?q, [a]) = ?q' \<and> m2 = \<pi>\<^sub>1 (SST.eta_hat sst2 (?q, [a]))"
      using m by (simp add:)
    have "delta_hat sst2 (q2, w1 @ [a]) = delta sst2 (hat1 (delta2f f (delta sst2)) (q2, xs), a)"
      by (simp add: w1 w2)
    moreover have "\<pi>\<^sub>1 (SST.eta_hat sst2 (q2, w1 @ [a])) = m"
      by (simp add: SST.eta_append resolve_shuffle_distrib m w1 w2)
    ultimately show "\<exists>w. delta_hat sst2 (q2, w) = delta sst2 (hat1 (delta2f f (delta sst2)) (q2, xs), a) \<and>
                         \<pi>\<^sub>1 (SST.eta_hat sst2 (q2, w)) = m"
      by (auto simp del: delta_append)
  qed
qed

theorem compose_typable:
  fixes sst2 :: "('q2::finite, 'x2::finite, 'b, 'c) SST"
  assumes "bounded_copy_SST k sst2"
  assumes "trim sst2"
  shows "bctype k (compose_SST_SST sst1 sst2) (compose_\<gamma> sst1 sst2)"
proof (auto simp add: bctype_def)
  show "bctype_idS k (compose_SST_SST sst1 sst2) (compose_\<gamma> sst1 sst2)"
    unfolding compose_SST_SST_def bctype_idS_def
    apply (auto simp add: all_shuffles_def)
    apply (rule exI[where x="[]"])
    apply (simp add: resolve_idU_idS)
    done
next
  show "bctype_step k (compose_SST_SST sst1 sst2) (compose_\<gamma> sst1 sst2)"
    unfolding bctype_step_def
    by (auto simp add: compose_SST_SST_def compose_\<delta>_def compose_\<eta>_def compose_\<gamma>_subset)
next
  show "bctype_bounded k (compose_SST_SST sst1 sst2) (compose_\<gamma> sst1 sst2)"
    unfolding bctype_bounded_def 
  proof (auto simp add: all_shuffles_def)
    fix q2 w
    have q2_reach: "reachable sst2 q2"
      using assms(2) unfolding trim_def by simp
    have "bounded k (SST.eta_hat sst2 (q2, w))"
      by (rule bounded_copy_SST_simp, simp_all add: assms q2_reach)
    then show "bounded_shuffle k (\<pi>\<^sub>1 (SST.eta_hat sst2 (q2, w)))"
      by (rule resolve_bounded)
  qed
next
  show "bctype_tails k (compose_SST_SST sst1 sst2) (compose_\<gamma> sst1 sst2)"
    unfolding bctype_tails_def
  proof (auto)
    fix q1 f q2 w x u m
    assume "reachable (compose_SST_SST sst1 sst2) (q1, f)"
    let ?eta = "SST.eta_hat (compose_SST_SST sst1 sst2) ((q1, f), w) (q2, x)"
    assume u: "u \<in> tails ?eta"
    assume m0: "m \<in> type_hom (compose_\<gamma> sst1 sst2) ((q1, f), u)"
    obtain v1 v2 where v: "u = Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) 
                                   (hat1 (delta2f f (delta sst2)) (q2, v1), v2)" using tail_substring_ex[OF u] by auto
    let ?q = "hat1 (delta2f f (delta sst2)) (q2, v1)"
    have m: "m \<in> type_hom (compose_\<gamma> sst1 sst2) ((q1, f), Transducer.hat2 (delta2f f (delta sst2)) (eta2f (eta sst2)) 
                                                 (?q, v2))" 
      using m0 v by simp
    obtain w where w: "\<pi>\<^sub>1 (SST.eta_hat sst2 (?q, w)) = m"
      using type_hom_eta2f_hat_ex_string[rule_format, OF m] by auto
    have q2_reach: "reachable sst2 ?q"
      using assms(2) unfolding trim_def by simp
    then have "bounded k (SST.eta_hat sst2 (?q, w))"
      using assms(1) unfolding bounded_copy_SST_def by simp
    then have "bounded_shuffle k (\<pi>\<^sub>1 (SST.eta_hat sst2 (?q, w)))"
      by (simp add: resolve_bounded)
    then show "bounded_shuffle k m" using w by simp
  qed
qed


end
