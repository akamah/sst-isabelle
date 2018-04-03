theory SingleUse
imports Main Setsum
begin
definition count_var :: "[('a::finite) \<Rightarrow> 'a list, 'a] \<Rightarrow> nat" where
  "count_var f x == sum (\<lambda>y. count_list (f y) x) UNIV"

lemma "count_list (f y) x \<le> count_var f x"
proof -
  have "sum (%y. count_list (f y) x) UNIV = sum (%y. count_list (f y) x) (UNIV - {y}) + (%y. count_list (f y) x) y"
    by (simp add: add.commute sum.remove)
  thus ?thesis
    by (simp add: count_var_def)
qed

definition bounded :: "[nat, ('a::finite) => 'a list] => bool" where
  "bounded k f = (\<forall>x. count_var f x \<le> k)"

definition single_use  :: "(('a::finite) \<Rightarrow> 'a list) \<Rightarrow> bool" where
  "single_use f = bounded 1 f"

lemma [simp]:  "count_list (xs@ys) a = count_list xs a + count_list ys a"
  by (induct xs, auto)


lemma basic_count: "count_list (concat (map f xs)) a =
                    sum (\<lambda>b. count_list (f b) a * count_list xs b) (UNIV::('a::finite) set)"
proof (induct xs)
  case Nil
  show ?case
    by (auto)
next
  case (Cons b xs)
  show ?case

  proof (simp)
    let ?g = "(\<lambda>ba. if b = ba then count_list (f ba) a else 0)"
    let ?h = "(\<lambda>ba. count_list (f ba) a * (count_list xs ba))"
    have "sum (\<lambda>ba. count_list (f ba) a * (if b = ba then count_list xs ba + 1 else count_list xs ba)) UNIV =
          sum (%x. ?g x + ?h x) UNIV"
      by(rule cong[of "%f. sum f UNIV" "%f. sum f UNIV"], auto)
    also have "sum (%x. ?g x + ?h x) UNIV = sum ?g UNIV + sum ?h UNIV"
      by (rule sum.distrib)
    finally have "sum (\<lambda>ba. count_list (f ba) a * (if b = ba then count_list xs ba + 1 else count_list xs ba)) UNIV
             = sum ?g UNIV + sum ?h UNIV"
      by simp
    thus "count_list (f b) a + count_list (concat (map f xs)) a =
sum (\<lambda>ba. count_list (f ba) a * (if b = ba then count_list xs ba + 1 else count_list xs ba))
 UNIV"
    proof (simp)
      show "count_list (f b) a + count_list (concat (map f xs)) a =
            (\<Sum>ba\<in>UNIV. if b = ba then count_list (f ba) a else 0) +
            (\<Sum>ba\<in>UNIV. count_list (f ba) a * count_list xs ba)"
      proof (rule cong[of "op + _" "op + _"], rule cong[of "op +" "op +"],simp)
        have "(\<Sum>ba\<in>(insert b (UNIV - {b})). if b = ba then count_list (f ba) a else 0) =
              (%ba. if b = ba then count_list (f ba) a else 0) b +
              (\<Sum>ba\<in>(UNIV - {b}). if b = ba then count_list (f ba) a else 0)"
          by(rule sum.insert, auto)
        thus "count_list (f b) a = (\<Sum>ba\<in>UNIV. if b = ba then count_list (f ba) a else 0)"
          by (simp del: sum.insert add: insert_UNIV)
      next
        show "count_list (concat (map f xs)) a = (\<Sum>ba\<in>UNIV. count_list (f ba) a * count_list xs ba)"
          by (rule Cons)
      qed
    qed
  qed
qed


lemma assumes "single_use f" "single_use g"
  shows "single_use (concat o (map f) o g)"
  unfolding single_use_def bounded_def
proof (rule allI)
  have[rule_format, simp]: "\<forall>x y. count_list (g y) x \<le> Suc 0"
  proof (intro  allI)
    fix x y
    show "count_list (g y) x \<le> Suc 0"
    proof (rule sumk[of UNIV y], auto)
      from assms
      have "count_var g x \<le> Suc 0"
        by (simp add: single_use_def bounded_def)
      thus "(\<Sum>a\<in>UNIV. count_list (g a) x) \<le> Suc 0"
        by (simp add: count_var_def)
    qed
  qed
  fix x
  show "count_var (concat \<circ> map f \<circ> g) x \<le> 1"
  proof (auto simp add: count_var_def)
    from assms
    have "count_var f x \<le> Suc 0"
      by (simp add: single_use_def bounded_def)
    hence "count_var f x = 0 \<or> count_var f x = Suc 0"
      by auto
    thus "(\<Sum>y\<in>UNIV. count_list (concat (map f (g y))) x) \<le> Suc 0"
    proof
      assume "count_var f x = 0"
      hence [simp]: "\<forall>y. count_list (f y) x = 0"
        unfolding count_var_def
        by(auto)
      show ?thesis
        by (simp add: basic_count)
    next
      assume a1: "count_var f x = Suc 0"
      show ?thesis
      proof (simp add: basic_count)
        have "\<exists>y \<in> UNIV. (%y. count_list (f y) x) y = 1 \<and> sum (%y. count_list (f y) x) (UNIV - {y}) = 0"
          by(rule sum1, simp, insert a1, simp add: count_var_def)
        then obtain z where z: "(%y. count_list (f y) x) z = 1"
          "sum (%y. count_list (f y) x) (UNIV - {z}) = 0"
          by auto
        have "(\<Sum>y\<in>UNIV. \<Sum>b\<in>UNIV. count_list (f b) x * count_list (g y) b)
            \<le> (\<Sum>y\<in>UNIV. count_list (g y) z)"
        proof (rule sum_mono)
          fix y
          have "(\<Sum>b\<in>UNIV. count_list (f b) x * count_list (g y) b) =
                (\<Sum>b\<in>(insert z (UNIV - {z})). count_list (f b) x * count_list (g y) b)"
            by(simp add: insert_UNIV)
          also have "... = count_list (f z) x * count_list (g y) z +
             (\<Sum>b\<in>(UNIV - {z}). count_list (f b) x * count_list (g y) b)"
            by (rule sum.insert, auto)
          also have "... =  count_list (g y) z"
            using z by(simp)
          finally show "(\<Sum>b\<in>UNIV. count_list (f b) x * count_list (g y) b) \<le>
            count_list (g y) z"
            by simp
        qed
        also have "... \<le> Suc 0"
          using assms by (simp add: single_use_def bounded_def count_var_def)
        finally show "(\<Sum>y\<in>UNIV. \<Sum>b\<in>UNIV. count_list (f b) x * count_list (g y) b) \<le> Suc 0"
          by simp
      qed
    qed
  qed
qed

end
