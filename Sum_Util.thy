(* Title:  Sum_Util.thy
   Author: Minamide Yasuhiko, Akama Hitoshi
*)

theory Sum_Util
  imports Sum_Type List
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

lemma is_inl_iff[iff]: "is_inl a \<longleftrightarrow> (\<exists>x. a = Inl x)"
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

primrec is_inr :: "('a + 'b) \<Rightarrow> bool" where
  "is_inr (Inl l) = False" |
  "is_inr (Inr r) = True"

lemma is_inr_iff[iff]: "is_inr a \<longleftrightarrow> (\<exists>x. a = Inr x)"
proof
  assume *: "is_inr a"
  then show "is_inr a \<Longrightarrow> (\<exists>x. a = Inr x)" proof (cases a)
    case (Inl a)
    then show ?thesis using * by auto
  next
    case (Inr b)
    then show ?thesis by simp
  qed
next
  assume "\<exists>x. a = Inr x"
  then obtain x where "a = Inr x" by auto
  then show "is_inr a" by simp
qed

primrec drop_left :: "('a + 'b) \<Rightarrow> 'b list" where
  "drop_left (Inl l) = []" |
  "drop_left (Inr r) = [r]" 

primrec drop_right :: "('a + 'b) \<Rightarrow> 'a list" where
  "drop_right (Inl l) = [l]" |
  "drop_right (Inr r) = []" 


definition concat_map :: "('b \<Rightarrow> 'c list) \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> 'c list" (infixl "\<odot>" 55) where
  "concat_map f g = concat o map f o g"

lemma concat_map_apply: "(f \<odot> g) x = concat (map f (g x))"
  unfolding concat_map_def by simp

lemma concat_map_lem: "concat (map (concat o map f o g) xs) = concat (map f (concat (map g xs)))"
  by (induct xs, auto simp add: concat_map_apply)

lemma concat_map_assoc: "(f \<odot> g) \<odot> h = f \<odot> (g \<odot> h)"
  by (auto simp add: concat_map_lem concat_map_def)


end