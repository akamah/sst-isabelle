(* Title:   Update.thy
   Author:  Akama Hitoshi
*)

theory Update
  imports Main List
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


subsection \<open>new induction rule\<close>

fun is_Some where
  "is_Some None = False" |
  "is_Some (Some a) = True"

fun is_Inl where
  "is_Inl (Inl a) = True" |
  "is_Inl (Inr b) = False"

lemma find_last:
  assumes "\<not> P a"
  shows "find P (xs @ [a]) = find P xs"
  using assms by (induct xs, simp_all)

lemma find_var_None_then_all_alpha:
  assumes "find is_Inl xs = None"
  shows "\<exists>u. xs = map Inr u"
using assms proof (induct xs rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case by simp
next
  case (Alpha a xs)
  then have "find is_Inl xs = None" by simp
  then obtain u where "xs = map Inr u" using Alpha.hyps by blast
  then show ?case by (metis list.simps(9))
qed

lemma find_split:
  assumes "is_Some (List.find P lis)"
  shows "\<exists>l x r. ((l @ x # r = lis) \<and> find P r = None \<and> P x)"
using assms proof (induction lis rule: rev_induct)
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
    then have "is_Some (find P as)"
      using False find_last snoc.prems by fastforce
    then obtain l x r where "l @ x # r = as \<and> find P r = None \<and> P x" using snoc.IH by blast
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
  then show ?case proof (cases "List.find is_Inl xs")
    case None
    then obtain v where "xs = map Inr v" using find_var_None_then_all_alpha by auto
    then show ?thesis by (simp add: word[of "v"])
  next
    case (Some a)
    then obtain l x r where hoge: "(xs = l @ x # r) \<and> List.find is_Inl r = None \<and> is_Inl x"
      by (metis find_split is_Some.simps(2))
    obtain v where v: "r = map Inr v" using find_var_None_then_all_alpha hoge by auto
    obtain x' where x': "x = Inl x'" using hoge is_Inl.elims(2) by blast
    have "P (l @ Inl x' # map Inr v)" proof (rule var_word)
      show "P l" by (rule IH[rule_format], simp add: hoge)
    qed
    then show ?thesis by (simp add: v x' hoge)
  qed
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

lemma concatU_append: "concatU (u @ v) = concatU u \<bullet> concatU v"
  by (induct u arbitrary: v, simp_all add: comp_left_neutral comp_assoc)

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

lemma map_alpha_idU[simp]: "t \<star> idU = idU"
  by (auto simp add: idU_def map_alpha_def )

lemma map_alpha_concatU: "t \<star> concatU us = concatU (map (op \<star> t) us)"
  by (induct us, simp_all add: map_alpha_distrib)
    
  

end
