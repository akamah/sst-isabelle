theory Update
imports Main 
begin

primrec fold_sum :: "['a \<Rightarrow> 'c, 'b \<Rightarrow> 'c, 'a + 'b] \<Rightarrow> 'c" where
  "fold_sum f g (Inl x) = f x" |
  "fold_sum f g (Inr y) = g y"


type_synonym ('a, 'b) update = "'a \<Rightarrow> ('a + 'b) list"

definition idU :: "('a, 'b) update" where
  "idU x == [Inl x]"

definition update2hom :: "('a, 'b) update \<Rightarrow> ('a + 'b) \<Rightarrow> ('a + 'b) list" where
  "update2hom f = fold_sum f (\<lambda>b. [Inr b])"


lemma [simp]: "update2hom f (Inl x) = f x"  
  by(auto simp add: update2hom_def)
    
lemma [simp]: "update2hom f (Inr x) = [Inr x]"  
  by(auto simp add: update2hom_def idU_def) 
   
definition hat_hom :: "('a, 'b) update \<Rightarrow> ('a + 'b) list \<Rightarrow> ('a + 'b) list" where
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
    
lemma [simp]: "hat_hom f (Inr a#xs) = [Inr a] @ hat_hom f xs"
  by (simp add: hat_hom_def)
    
lemma [simp]: "hat_hom f (xs@ys) = hat_hom f xs @ hat_hom f ys"
  by (simp add: hat_hom_def)

(* lemma hat_hom_map "hat_hom f (map  *)

lemma hat_hom_right_ignore: "hat_hom f (map Inr xs) = map Inr xs"  
  by (induction xs, auto)

definition comp :: "[ ('a, 'b) update,  ('a, 'b) update] \<Rightarrow>  ('a, 'b) update" where
  "comp f g == (hat_hom f) o g"
  
lemma comp_lem: "hat_hom f (hat_hom g xs) = hat_hom (hat_hom f o g) xs"
proof (induct xs)
  case Nil
  show ?case
    by simp
next
  fix a xs
  case (Cons a xs)
  thus ?case
    by(cases a, simp_all)
qed

lemma comp_assoc: "comp f (comp g h) = comp (comp f g) h"
  by (auto simp add: comp_def comp_lem)

lemma comp_left_neutral: "comp idU f = f"
  by (auto simp add: comp_def idU_def)

lemma comp_right_neutral: "comp f idU = f"
  by (auto simp add: comp_def idU_def)

end
  