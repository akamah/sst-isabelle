(* Title:  Sum_Util.thy
   Author: Minamide Yasuhiko, Akama Hitoshi
*)

theory Sum_Util
  imports HOL.Sum_Type HOL.List
begin


primrec fold_sum :: "('a \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'c) \<Rightarrow> ('a + 'b \<Rightarrow> 'c)" where
  "fold_sum f g (Inl x) = f x" |
  "fold_sum f g (Inr y) = g y"

fun inl_list :: "'a \<Rightarrow> ('a + 'b) list" where
  "inl_list x = [Inl x]"

fun inr_list :: "'b \<Rightarrow> ('a + 'b) list" where
  "inr_list y = [Inr y]"

lemma ext_sum:
  assumes "\<And>l. f (Inl l) = g (Inl l)"
  assumes "\<And>r. f (Inr r) = g (Inr r)"
  shows "f = g"
proof
  fix x
  show "f x = g x" using assms by (cases x, simp_all)
qed


lemma map_sum_comp: "map_sum (f1 o f2) (g1 o g2) = map_sum f1 g1 \<circ> map_sum f2 g2"
  by (rule ext_sum, simp_all)

lemma fold_sum_comp: "fold_sum (f1 o g1) (f2 o g2) = fold_sum f1 f2 o map_sum g1 g2"
  by (rule ext_sum, simp_all)

lemma map_sum_eq_fold_sum: "map_sum f g = fold_sum (Inl o f) (Inr o g)"
  by (rule ext_sum, simp_all)

fun const :: "'a \<Rightarrow> 'b \<Rightarrow> 'a" where
  "const a b = a"

primrec is_inl :: "('a + 'b) \<Rightarrow> bool" where
  "is_inl (Inl l) = True" |
  "is_inl (Inr r) = False"

lemma is_inl_iff: "is_inl a \<longleftrightarrow> (\<exists>x. a = Inl x)"
proof
  assume *: "is_inl a"
  show "is_inl a \<Longrightarrow> (\<exists>x. a = Inl x)" proof (cases a)
    case (Inl a)
    then show ?thesis by auto
  next
    case (Inr b)
    then show ?thesis using * by simp
  qed
next
  assume "\<exists>x. a = Inl x"
  then obtain x where "a = Inl x" by auto
  then show "is_inl a" by simp
qed


primrec drop_left :: "('a + 'b) \<Rightarrow> 'b list" where
  "drop_left (Inl l) = []" |
  "drop_left (Inr r) = [r]" 

primrec drop_right :: "('a + 'b) \<Rightarrow> 'a list" where
  "drop_right (Inl l) = [l]" |
  "drop_right (Inr r) = []" 


definition cm_comp :: "('b \<Rightarrow> 'c list) \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> 'c list" (infixl "\<odot>" 55) where
  "cm_comp f g = concat o map f o g"

lemma cm_comp_apply[simp]: "(f \<odot> g) x = concat (map f (g x))"
  unfolding cm_comp_def by simp


definition id_cm_comp :: "'a \<Rightarrow> 'a list" where
  "id_cm_comp x = [x]"

declare id_cm_comp_def[simp]

lemma [simp]: "concat (map id_cm_comp xs) = xs"
  by (induct xs, simp_all)

lemma [simp]: "id_cm_comp \<odot> f = f"
  by (rule ext) simp

lemma [simp]: "f \<odot> id_cm_comp = f"
  by (rule ext) simp

lemma cm_comp_lem: "concat (map (f \<odot> g) xs) = concat (map f (concat (map g xs)))"
  by (induct xs, simp_all)

lemma cm_comp_assoc: "(f \<odot> g) \<odot> h = f \<odot> (g \<odot> h)"
  by (rule ext, simp add: cm_comp_lem)

thm comp_assoc

end