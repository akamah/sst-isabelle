(* Title:   Update.thy
   Author:  Akama Hitoshi
*)

theory Update
  imports Main HOL.List "../Util/Sum_Util" "../Core/Concat_Map"
begin



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


definition compU :: "[ ('y, 'z, 'b) update',  ('x, 'y, 'b) update'] \<Rightarrow>  ('x, 'z, 'b) update'" (infixl "\<bullet>" 55)
  where "compU f g = (hat_hom f) o g"

lemma compU_apply: "(f \<bullet> g) x = hat_hom f (g x)"
  by (simp add: compU_def)

lemma compU_lem: "hat_hom (f \<bullet> g) xs = hat_hom f (hat_hom g xs)"
  by (induct xs rule: xa_induct, simp_all add: compU_apply)

lemma compU_assoc: "(f \<bullet> g) \<bullet> h = f \<bullet> (g \<bullet> h)"
  by (rule ext, simp add: compU_lem compU_apply)

lemma compU_left_neutral[simp]: "idU \<bullet> f = f"
  by (auto simp add: compU_apply idU_def)

lemma compU_right_neutral[simp]: "f \<bullet> idU = f"
  by (auto simp add: compU_apply idU_def)

lemma compU_ignore: "(f \<bullet> (\<lambda>y. g a)) x = (f \<bullet> g) a"
  by (simp add: compU_apply)

lemma update2hom_compS_compU: "update2hom f \<odot> g = f \<bullet> g"
  by (rule ext, simp add: compU_apply compS_apply hat_hom_def)


fun concatU :: "('x, 'b) update list \<Rightarrow> ('x, 'b) update" where
  "concatU []     = idU" |
  "concatU (f#fs) = f \<bullet> concatU fs"

lemma concatU_append: "concatU (u @ v) = concatU u \<bullet> concatU v"
  by (induct u arbitrary: v, simp_all add: compU_assoc)

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

lemma [simp]: "hat_alpha idS xs = xs"
  by (induct xs rule: xa_induct, simp_all add: compS_apply, simp add: idS_def)

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
  by (rule ext, simp add: map_alpha_apply hat_alpha_hat_hom_lem compU_apply)

lemma map_alpha_idU[simp]: "t \<star> idU = idU"
  by (rule ext, simp add: idU_def map_alpha_apply)

lemma map_alpha_concatU: "t \<star> concatU us = concatU (map (map_alpha t) us)"
  by (induct us, simp_all add: map_alpha_distrib)

lemma map_alpha_lem: "hat_alpha s (hat_alpha t u) = hat_alpha (s \<odot> t) u"
  by (induct u rule: xa_induct, simp_all add: compS_apply hat_alpha_right_map)

lemma map_alpha_assoc: "s \<star> (t \<star> f) = (s \<odot> t) \<star> f"
  by (rule ext, simp add: map_alpha_apply map_alpha_lem)

lemma idS_map_alpha[simp]: "idS \<star> m = m"
  by (rule ext, simp add: map_alpha_apply)

lemma alpha_hom_compS_map_alpha: "alpha_hom t \<odot> m = t \<star> m"
  by (rule ext, simp add: compS_apply map_alpha_apply hat_alpha_def)

end
