(* Title:   Update.thy
   Author:  Akama Hitoshi
*)

theory Update
  imports Main HOL.List "../Util/Sum_Util"
begin

(* an induct rule for variable and alphabet list *)
(* [consumes n] to skip first n assumptions at induct phase *)
lemma xa_induct [consumes 0, case_names Nil Var Alpha]:
  "P [] \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (Inl x#xs))
        \<Longrightarrow> (\<And>a xs. P xs \<Longrightarrow> P (Inr a#xs))
        \<Longrightarrow> P xs"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons a xs) then show ?case by (cases a) simp_all
qed

lemma xa_rev_induct [consumes 0, case_names Nil Var Alpha]:
  "P [] \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (xs @ [Inl x]))
        \<Longrightarrow> (\<And>a xs. P xs \<Longrightarrow> P (xs @ [Inr a]))
        \<Longrightarrow> P xs"
proof (induct xs rule: rev_induct)
  case Nil then show ?case by simp
next
  case (snoc a xs) then show ?case by (cases a) simp_all
qed


subsection \<open>new induct rule\<close>

lemma find_last:
  assumes "\<not> P a"
  shows "find P (xs @ [a]) = find P xs"
  using assms by (induct xs, simp_all)

lemma find_var_None_then_all_alpha:
  assumes "find isl xs = None"
  shows "\<exists>u. xs = map Inr u"
using assms proof (induct xs rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case by simp
next
  case (Alpha a xs)
  then obtain u where u: "xs = map Inr u" by auto
  then show ?case proof -
    have "Inr a # xs = map Inr (a # u)" using u by simp
    then show ?thesis by (rule exI)
  qed
qed

lemma find_split:
  assumes "List.find P lis \<noteq> None"
  shows "\<exists>l x r. ((l @ x # r = lis) \<and> find P r = None \<and> P x)"
using assms proof (induct lis rule: rev_induct)
  case Nil
  then show ?case by simp 
next
  case (snoc a as)
  then show ?case proof (cases "P a")
    case True 
    then have "as @ a # [] = as @ [a] \<and> find P [] = None \<and> P a" by simp
    then show ?thesis by blast
  next
    case False
    then have "find P as \<noteq> None"
      using False find_last snoc.prems by fastforce
    then obtain l x r where "l @ x # r = as \<and> find P r = None \<and> P x" using snoc by blast
    then have "l @ x # (r @ [a]) = as @ [a] \<and> find P (r @ [a]) = None \<and> P x" by (simp add: False find_last)
    then show ?thesis by blast
  qed
qed

lemma xw_induct [case_names Word VarWord]:
  assumes word: "(\<And>w. P (map Inr w))"
  assumes var_word: "(\<And>x w u. P u \<Longrightarrow> P (u @ Inl x # map Inr w))"
  shows "P u"
proof (induct u rule: length_induct)
  case IH: (1 xs)
  then show ?case proof (cases "List.find isl xs")
    case None
    then obtain v where "xs = map Inr v" using find_var_None_then_all_alpha by auto
    then show ?thesis by (simp add: word[of "v"])
  next
    case (Some a)
    then have "find isl xs \<noteq> None" by simp
    then obtain l x r where hoge: "(xs = l @ x # r) \<and> find isl r = None \<and> isl x"
      using find_split[where P="isl", where lis="xs"] by blast
    obtain v where v: "r = map Inr v" using find_var_None_then_all_alpha hoge by blast
    obtain x' where x': "x = Inl x'"
      using hoge by (meson isl_def)
    have "P (l @ Inl x' # map Inr v)" proof (rule var_word)
      show "P l" by (rule IH[rule_format], simp add: hoge)
    qed
    then show ?thesis by (simp add: v x' hoge)
  qed
qed


type_synonym ('a, 'b) update = "'a \<Rightarrow> ('a + 'b) list"
type_synonym ('x, 'y, 'b) update' = "'x \<Rightarrow> ('y + 'b) list"

definition idU :: "('a, 'b) update" where
  "idU x == [Inl x]"

definition emptyU :: "('x, 'b) update" where
  "emptyU x = []"

definition update2hom :: "('x, 'y, 'b) update' \<Rightarrow> ('x + 'b) \<Rightarrow> ('y + 'b) list" where
  "update2hom f = fold_sum f inr_list"


lemma [simp]: "update2hom f (Inl x) = f x"
  by (auto simp add: update2hom_def)

lemma [simp]: "update2hom f (Inr x) = [Inr x]"
  by (auto simp add: update2hom_def idU_def)

definition hat_hom :: "('x, 'y, 'b) update' \<Rightarrow> ('x + 'b) list \<Rightarrow> ('y + 'b) list" where
  "hat_hom f = concat o map (update2hom f)"

lemma [simp]: "update2hom idU x = [x]"
  by (simp add: update2hom_def fold_sum_def idU_def sum.case_eq_if)

lemma [simp]: "hat_hom idU = id"
proof
  fix x :: "('a + 'b) list"
  show "hat_hom idU x = id x"
    by (induct x, auto simp add: hat_hom_def)
qed

lemma [simp]: "hat_hom f [] = []"
  by (simp add: hat_hom_def)

lemma [simp]: "hat_hom f (Inl a#xs) = f a @ hat_hom f xs"
  by (simp add: hat_hom_def)

lemma [simp]: "hat_hom f (Inr a#xs) = Inr a # hat_hom f xs"
  by (simp add: hat_hom_def)

lemma [simp]: "hat_hom f (xs@ys) = hat_hom f xs @ hat_hom f ys"
  by (simp add: hat_hom_def)

lemma hat_hom_right_ignore[simp]: "hat_hom f (map Inr xs) = map Inr xs"
  by (induct xs, auto)

lemma hat_hom_left_concat_map[simp]: "hat_hom f (map Inl xs) = concat (map f xs)"
  by (induct xs, auto)


definition comp :: "[ ('y, 'z, 'b) update',  ('x, 'y, 'b) update'] \<Rightarrow>  ('x, 'z, 'b) update'" (infixl "\<bullet>" 55)
  where "comp f g = (hat_hom f) o g"

lemma comp_apply: "(f \<bullet> g) x = hat_hom f (g x)"
  by (simp add: comp_def)

lemma comp_lem: "hat_hom (f \<bullet> g) xs = hat_hom f (hat_hom g xs)"
  by (induct xs rule: xa_induct, simp_all add: comp_apply)

lemma comp_assoc: "(f \<bullet> g) \<bullet> h = f \<bullet> (g \<bullet> h)"
  by (rule ext, simp add: comp_lem comp_apply)

(* auto simp add: comp_def comp_lem) *)

lemma comp_left_neutral[simp]: "comp idU f = f"
  by (auto simp add: comp_def idU_def)

lemma comp_right_neutral[simp]: "comp f idU = f"
  by (auto simp add: comp_def idU_def)

lemma comp_ignore: "(f \<bullet> (\<lambda>y. g a)) x = (f \<bullet> g) a"
  by (simp add: comp_def)

fun concatU :: "('x, 'b) update list \<Rightarrow> ('x, 'b) update" where
  "concatU []     = idU" |
  "concatU (f#fs) = f \<bullet> concatU fs"

lemma concatU_append: "concatU (u @ v) = concatU u \<bullet> concatU v"
  by (induct u arbitrary: v, simp_all add: comp_assoc)

definition alpha_hom :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'x + 'a \<Rightarrow> ('x + 'b) list" where
  "alpha_hom f = fold_sum inl_list (\<lambda>a. map Inr (f a))"

lemma [simp]: "alpha_hom f (Inl x) = [Inl x]"
  by (simp add: alpha_hom_def)

lemma [simp]: "alpha_hom f (Inr a) = map Inr (f a)"
  by (simp add: alpha_hom_def)


definition hat_alpha :: "('a \<Rightarrow> 'b list) \<Rightarrow> ('x + 'a) list \<Rightarrow> ('x + 'b) list" where
  "hat_alpha f = concat o map (alpha_hom f)"

lemma [simp]: "hat_alpha t [] = []"
  by (simp add: hat_alpha_def)

lemma [simp]: "hat_alpha t (Inl x#xs) = Inl x # hat_alpha t xs"
  by (simp add: hat_alpha_def)

lemma [simp]: "hat_alpha t (Inr a#xs) = map Inr (t a) @ hat_alpha t xs"
  by (simp add: hat_alpha_def)

lemma [simp]: "hat_alpha t (xs@ys) = hat_alpha t xs @ hat_alpha t ys"
  by (simp add: hat_alpha_def)

lemma [simp]: "hat_alpha id_cm_comp xs = xs"
  by (induct xs rule: xa_induct, simp_all add: cm_comp_apply, simp add: id_cm_comp_def)

lemma hat_alpha_left_ignore: "hat_alpha f (map Inl xs) = map Inl xs"
  by (induct xs, auto)

lemma hat_alpha_right_map: "hat_alpha f (map Inr as) = map Inr (concat (map f as))"
  by (induct as, auto)


definition map_alpha :: "('a \<Rightarrow> 'b list) \<Rightarrow> ('x, 'y, 'a) update' \<Rightarrow> ('x, 'y, 'b) update'" (infix "\<star>" 60)
  where "map_alpha t m = hat_alpha t o m"

lemma map_alpha_apply: "(t \<star> m) x = hat_alpha t (m x)"
  unfolding map_alpha_def by simp

lemma hat_alpha_hat_hom_lem: "hat_alpha t (hat_hom f w) = hat_hom (t \<star> f) (hat_alpha t w)"
  by (induct w rule: xa_induct, simp_all add: map_alpha_apply)

lemma map_alpha_distrib: "t \<star> (\<psi> \<bullet> \<phi>) = t \<star> \<psi> \<bullet> t \<star> \<phi>"
  by (rule ext, simp add: map_alpha_apply hat_alpha_hat_hom_lem comp_apply)

lemma map_alpha_idU[simp]: "t \<star> idU = idU"
  by (rule ext, simp add: idU_def map_alpha_apply)

lemma map_alpha_concatU: "t \<star> concatU us = concatU (map (map_alpha t) us)"
  by (induct us, simp_all add: map_alpha_distrib)

lemma map_alpha_lem: "hat_alpha s (hat_alpha t u) = hat_alpha (s \<odot> t) u"
  by (induct u rule: xa_induct, simp_all add: cm_comp_apply hat_alpha_right_map)

lemma map_alpha_assoc: "s \<star> (t \<star> f) = (s \<odot> t) \<star> f"
  by (rule ext, simp add: map_alpha_apply map_alpha_lem)

lemma id_cm_comp_map_alpha[simp]: "id_cm_comp \<star> m = m"
  by (rule ext, simp add: map_alpha_apply)

end
