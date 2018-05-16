(* Title:  Sum_Util.thy
   Author: Akama Hitoshi
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


end