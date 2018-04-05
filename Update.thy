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


definition comp :: "[ ('y, 'z, 'b) update',  ('x, 'y, 'b) update'] \<Rightarrow>  ('x, 'z, 'b) update'" (infixl "\<bullet>" 55)
  where "comp f g == (hat_hom f) o g"

lemma comp_lem: "hat_hom f (hat_hom g xs) = hat_hom (hat_hom f o g) xs"
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons a xs)
  thus ?case by (cases a, simp_all)
qed

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

end
