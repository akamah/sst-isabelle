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

end