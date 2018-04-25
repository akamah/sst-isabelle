(* Title:   Update.thy
   Author:  Akama Hitoshi
*)

theory Update
  imports Main
begin

(* an induction rule for variable and alphabet list *)
(* [consumes n] to skip first n assumptions at induction phase *)
lemma xa_induct [consumes 0, case_names Nil Var Alpha]:
  "P [] \<Longrightarrow> (\<And>x xs. P xs \<Longrightarrow> P (Inl x#xs))
        \<Longrightarrow> (\<And>a xs. P xs \<Longrightarrow> P (Inr a#xs))
        \<Longrightarrow> P xs"
proof (induction xs)
  case Nil then show ?case by simp
next
  case (Cons a xs) then show ?case by (cases a) simp_all
qed

primrec fold_sum :: "['a \<Rightarrow> 'c, 'b \<Rightarrow> 'c, 'a + 'b] \<Rightarrow> 'c" where
  "fold_sum f g (Inl x) = f x" |
  "fold_sum f g (Inr y) = g y"


type_synonym ('a, 'b) update = "'a \<Rightarrow> ('a + 'b) list"
type_synonym ('x, 'y, 'b) update' = "'x \<Rightarrow> ('y + 'b) list"

definition idU :: "('a, 'b) update" where
  "idU x == [Inl x]"

definition emptyU :: "('x, 'b) update" where
  "emptyU x = []"

definition update2hom :: "('x, 'y, 'b) update' \<Rightarrow> ('x + 'b) \<Rightarrow> ('y + 'b) list" where
  "update2hom f = fold_sum f (\<lambda>b. [Inr b])"


lemma [simp]: "update2hom f (Inl x) = f x"
  by(auto simp add: update2hom_def)

lemma [simp]: "update2hom f (Inr x) = [Inr x]"
  by(auto simp add: update2hom_def idU_def)

definition hat_hom :: "('x, 'y, 'b) update' \<Rightarrow> ('x + 'b) list \<Rightarrow> ('y + 'b) list" where
  "hat_hom f = concat o map (update2hom f)"

lemma [simp]: "update2hom idU x = [x]"
  by (simp add: update2hom_def fold_sum_def idU_def sum.case_eq_if)

lemma [simp]: "hat_hom idU = id"
proof
  fix x :: "('a + 'b) list"
  show "hat_hom idU x = id x"
    by (induction x, auto simp add: hat_hom_def)
qed

lemma [simp]: "hat_hom f [] = []"
  by (simp add: hat_hom_def)

lemma [simp]: "hat_hom f (Inl a#xs) = f a @ hat_hom f xs"
  by (simp add: hat_hom_def)

lemma [simp]: "hat_hom f (Inr a#xs) = Inr a # hat_hom f xs"
  by (simp add: hat_hom_def)

lemma [simp]: "hat_hom f (xs@ys) = hat_hom f xs @ hat_hom f ys"
  by (simp add: hat_hom_def)

lemma hat_hom_right_ignore: "hat_hom f (map Inr xs) = map Inr xs"
  by (induction xs, auto)

lemma hat_hom_left_concat_map: "hat_hom f (map Inl xs) = concat (map f xs)"
  by (induction xs, auto)


definition comp :: "[ ('y, 'z, 'b) update',  ('x, 'y, 'b) update'] \<Rightarrow>  ('x, 'z, 'b) update'" (infixl "\<bullet>" 55)
  where "comp f g == (hat_hom f) o g"

lemma comp_lem: "hat_hom f (hat_hom g xs) = hat_hom (hat_hom f o g) xs"
  by (induct xs rule: xa_induct, simp_all)

lemma comp_assoc: "(f \<bullet> g) \<bullet> h = f \<bullet> (g \<bullet> h)"
  by (auto simp add: comp_def comp_lem)

lemma comp_left_neutral: "comp idU f = f"
  by (auto simp add: comp_def idU_def)

lemma comp_right_neutral: "comp f idU = f"
  by (auto simp add: comp_def idU_def)

lemma comp_ignore: "(f \<bullet> (\<lambda>y. g a)) x = (f \<bullet> g) a"
  by (simp add: comp_def)

fun concatU :: "('x, 'b) update list \<Rightarrow> ('x, 'b) update" where
  "concatU []     = idU" |
  "concatU (f#fs) = f \<bullet> concatU fs"




definition alpha_hom :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'x + 'a \<Rightarrow> ('x + 'b) list" where
  "alpha_hom f = fold_sum (\<lambda>x. [Inl x]) (\<lambda>a. map Inr (f a))"

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

lemma hat_alpha_left_ignore: "hat_alpha f (map Inl xs) = map Inl xs"
  by (induction xs, auto)

lemma hat_alpha_right_map: "hat_alpha f (map Inr as) = map Inr (concat (map f as))"
  by (induction as, auto)


definition map_alpha :: "('a \<Rightarrow> 'b list) \<Rightarrow> ('x, 'y, 'a) update' \<Rightarrow> ('x, 'y, 'b) update'" (infixl "\<star>" 60)
  where "map_alpha t f = hat_alpha t o f"

lemma alpha_lem: "hat_alpha t (hat_hom f w) = hat_hom (t \<star> f) (hat_alpha t w)"
  by (induct w rule: xa_induct, simp_all add: map_alpha_def hat_hom_right_ignore)

lemma map_alpha_distrib: "t \<star> (\<psi> \<bullet> \<phi>) = t \<star> \<psi> \<bullet> t \<star> \<phi>"
  by (auto simp add: alpha_lem map_alpha_def comp_def)


end
