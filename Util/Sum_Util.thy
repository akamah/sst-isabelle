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

lemma ext_prod:
  assumes "\<And>x y. f (x, y) = g (x, y)"
  shows "f = g"
proof
  fix x
  show "f x = g x" using assms by (cases x, simp)
qed

lemma map_sum_comp: "map_sum (f1 o f2) (g1 o g2) = map_sum f1 g1 \<circ> map_sum f2 g2"
  by (rule ext_sum, simp_all)

lemma fold_sum_comp: "fold_sum (f1 o g1) (f2 o g2) = fold_sum f1 f2 o map_sum g1 g2"
  by (rule ext_sum, simp_all)

lemma map_sum_eq_fold_sum: "map_sum f g = fold_sum (Inl o f) (Inr o g)"
  by (rule ext_sum, simp_all)

primrec retain_right :: "('a + 'b) \<Rightarrow> 'b list" where
  "retain_right (Inl l) = []" |
  "retain_right (Inr r) = [r]" 

primrec retain_left :: "('a + 'b) \<Rightarrow> 'a list" where
  "retain_left (Inl l) = [l]" |
  "retain_left (Inr r) = []" 

section \<open>Induction rules for "('a + 'b) list"\<close>

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
      using hoge unfolding isl_def by blast      
    have "P (l @ Inl x' # map Inr v)" proof (rule var_word)
      show "P l" by (rule IH[rule_format], simp add: hoge)
    qed
    then show ?thesis by (simp add: v x' hoge)
  qed
qed


hide_fact (open) find_last find_var_None_then_all_alpha find_split

end