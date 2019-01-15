(* Title:   Scan.thy
   Author:  Akama Hitoshi
*)


theory Scan
  imports HOL.List "../Util/Sum_Util"
begin

lemma pair_induct [case_names Nil PairCons]:
  assumes head: "P []"
  assumes pair: "\<And>x as xas. P xas \<Longrightarrow> P ((x, as)#xas)"
  shows "P xas"
proof (induct xas)
  case Nil
  then show ?case by (simp add: head)
next
  case (Cons ax xas)
  then show ?case proof (cases ax)
    case (Pair x as)
    then show ?thesis by (simp add: pair Cons)
  qed
qed

lemma pair_rev_induct [case_names Nil PairSnoc]:
  assumes head: "P []"
  assumes pair: "\<And>x as xas. P xas \<Longrightarrow> P (xas @ [(x, as)])"
  shows "P xas"
proof (induct xas rule: rev_induct)
  case Nil
  then show ?case by (simp add: head)
next
  case (snoc ax xas)
  then show ?case proof (cases ax)
    case (Pair x as)
    then show ?thesis by (simp add: pair snoc)
  qed
qed


subsubsection \<open>Scanned string\<close>

text \<open>Scanned string\<close>
type_synonym ('y, 'b) scanned_tail = "('y \<times> 'b list) list"
type_synonym ('y, 'b) scanned = "'b list \<times> ('y, 'b) scanned_tail"

fun length_scanned :: "('y, 'b) scanned \<Rightarrow> nat" where
  "length_scanned (w, xas) = Suc (length xas)"

definition append_scanned :: "('y, 'b) scanned \<Rightarrow> ('y, 'b) scanned_tail \<Rightarrow> ('y, 'b) scanned" (infixl "@@@" 80) where
  "append_scanned = (\<lambda>(w, xas) yas. (w, xas @ yas))"

lemma append_scanned_assoc: "(xas @@@ yas) @@@ zas = xas @@@ (yas @ zas)"
  by (cases xas, simp add: append_scanned_def)

lemma append_scanned_simp: "(w, xas) @@@ yas = (w, xas @ yas)"
  unfolding append_scanned_def by simp

lemma append_scanned_Nil[simp]: "xas @@@ [] = xas" 
  by (cases xas, simp add: append_scanned_def)

lemma fst_append_scanned[simp]: "fst (a @@@ b) = fst a"
  by (cases a, simp add: append_scanned_simp)

lemma length_scanned_gt: "length_scanned xas > 0"
  by (cases xas, simp)

lemma length_append_scanned_1: "length_scanned (xas @@@ [p]) = Suc (length_scanned xas)"
proof (cases xas)
  case (Pair w xs)
  then show ?thesis by (induct xs, simp_all add: append_scanned_simp)
qed

lemma length_Cons_scanned_1: "length_scanned (w, x # xas) = Suc (length_scanned (w, xas))"
  by (induct xas, simp_all add: append_scanned_simp)

lemma length_append_scanned[simp]:
  "length_scanned (xas @@@ ys) = length_scanned xas + length ys"
proof (induct ys arbitrary: xas rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case by (simp add: append_scanned_assoc[symmetric] length_append_scanned_1) 
qed

lemma scanned_induct_aux:
  assumes head: "\<And>w. P (w, [])"
  assumes pair: "\<And>w x as xas. (\<And>u. P (u, xas)) \<Longrightarrow> P ((w, [(x, as)]) @@@ xas)"
  shows "P (w, xs)"
proof (induct xs arbitrary: w rule: pair_induct)
  case Nil
  then show ?case using head by simp
next
  case (PairCons x as xas)
  then show ?case proof -
    have "P ((w, [(x, as)]) @@@ xas)" by (simp add: PairCons pair)
    then show ?thesis by (simp add: append_scanned_simp)
  qed
qed

lemma scanned_induct[case_names Nil PairCons]:
  assumes head: "\<And>w. P (w, [])"
  assumes pair: "\<And>w x as xas. (\<And>u. P (u, xas)) \<Longrightarrow> P ((w, [(x, as)]) @@@ xas)"
  shows "P sc"
  apply (cases sc)
  apply simp
  apply (rule scanned_induct_aux)
   apply (simp add: head)
  apply (simp add: pair)
  done

lemma scanned_rev_induct_aux:
  assumes head: "\<And>w. P (w, [])"
  assumes pair: "\<And>x as sc. P sc \<Longrightarrow> P (sc @@@ [(x, as)])"
  shows "P (w, xs)"
proof (induct xs rule: pair_rev_induct)
  case Nil
  then show ?case using head by simp
next
  case (PairSnoc x as xas)
  then show ?case proof -
    have "P ((w, xas) @@@ [(x, as)])" by (simp add: PairSnoc pair)
    then show ?thesis by (simp add: append_scanned_simp)
  qed
qed

lemma scanned_rev_induct[case_names Nil PairSnoc]:
  assumes head: "\<And>w. P (w, [])"
  assumes pair: "\<And>x as sc. P sc \<Longrightarrow> P (sc @@@ [(x, as)])"
  shows "P sc"
  using assms by (cases sc, simp add: scanned_rev_induct_aux)


subsubsection \<open>Scan\<close>

text \<open>scan var-alphabet list, and split it into a scanned string\<close>

fun scan_pair_rec :: "'y \<Rightarrow> 'b list \<Rightarrow> ('y + 'b) list \<Rightarrow> ('y, 'b) scanned_tail" where
  "scan_pair_rec x as [] = [(x, as)]" |
  "scan_pair_rec x as (Inl y#u) = (x, as) # scan_pair_rec y [] u" |
  "scan_pair_rec x as (Inr a#u) = scan_pair_rec x (as @ [a]) u"

fun scan_head :: "'b list \<Rightarrow> ('y + 'b) list \<Rightarrow> ('y, 'b) scanned" where
  "scan_head as [] = (as, [])" |
  "scan_head as (Inl x#u) = (as, scan_pair_rec x [] u)" |
  "scan_head as (Inr a#u) = scan_head (as @ [a]) u"

definition scan :: "('y + 'b) list \<Rightarrow> ('y, 'b) scanned" where
  "scan u = scan_head [] u"

definition scan_pair :: "('y + 'b) list \<Rightarrow> ('y \<times> 'b list) list" where
  "scan_pair u = snd (scan u)"

definition keys_pair :: "('y \<times> 'b list) list \<Rightarrow> 'y list" where
  "keys_pair ps = map fst ps"

fun map_value_pair :: "('b \<Rightarrow> 'c list) \<Rightarrow> ('y \<times> 'b list) list \<Rightarrow> ('y \<times> 'c list) list" where
  "map_value_pair f Nil = []" |
  "map_value_pair f ((y, bs)#ybs) = (y, concat (map f bs)) # map_value_pair f ybs"

definition map_value_scanned where
  "map_value_scanned f scanned = (map f (fst scanned), map_value_pair f (snd scanned))"

fun concat_value_pair where
  "concat_value_pair Nil = []" |
  "concat_value_pair ((x, as)#xas) = as @ concat_value_pair xas"

lemma concat_value_pair_last_simp[simp]:
  "concat_value_pair (xas @ [(x, as)]) = concat_value_pair xas @ as"
  by (induct xas rule: pair_induct, simp_all)

definition concat_value_scanned where
  "concat_value_scanned scanned = fst scanned @ concat_value_pair (snd scanned)"

lemma concat_value_scanned_Nil[simp]:
  "concat_value_scanned (as, []) = as"
  unfolding concat_value_scanned_def by simp

lemma concat_value_scanned_last_simp[simp]:
  "concat_value_scanned (sc @@@ [(x, as)]) = concat_value_scanned sc @ as"
proof (induct sc rule: scanned_induct)
  case (Nil w)
  then show ?case by (simp add: concat_value_scanned_def append_scanned_def)
next
  case (PairCons w x as xas)
  then show ?case by (simp add: concat_value_scanned_def append_scanned_def)
qed


lemma map_value_pair_last_simp[simp]:
  "map_value_pair f (ybs @ [(y, bs)]) = map_value_pair f ybs @ [(y, concat (map f bs))]"
  by (induct ybs rule: pair_induct, simp_all)

lemma keys_pair_map_value_pair:
  "keys_pair (map_value_pair f xas) = keys_pair xas"
  by (induct xas rule: pair_induct, simp_all add: keys_pair_def)

lemma keys_pair_Nil[simp]: "keys_pair [] = []" 
  unfolding keys_pair_def by simp

lemma keys_pair_Cons[simp]: "keys_pair ((x, as)#xas) = x # keys_pair xas"
  unfolding keys_pair_def by simp

lemma keys_pair_snoc[simp]: "keys_pair (xas @ [(x, as)]) = keys_pair xas @ [x]"
  unfolding keys_pair_def by simp



lemma scan_word_simp[simp]:
  "scan (map Inr w) = (w, [])"
proof -
  { fix as
    have "scan_head as (map Inr w) = (as @ w, [])"
      by (induct w arbitrary: as, simp_all)
  }
  note that = this
  then show ?thesis by (simp add: that scan_def)
qed

lemma scan_last_simp[simp]:
  "scan (u @ Inl x # map Inr w) = scan u @@@ [(x :: 'x, w)]"
proof -
  { fix y :: 'x and bs
    have "scan_pair_rec y bs (map Inr w) = [(y, bs @ w)]" by (induct w arbitrary: bs, simp_all)
  } note pair_alphabet = this
  { fix x y :: 'x and as u
    have "scan_pair_rec x as (u @ Inl y # map Inr w) = scan_pair_rec x as u @ [(y, w)]"
      by (induct u arbitrary: x y as rule: xa_induct, simp_all add: pair_alphabet)
  } note pair = this
  { fix as
    have "scan_head as (u @ Inl x # map Inr w) = scan_head as u @@@ [(x, w)]"
      by (induct u arbitrary: as rule: xa_induct, simp_all add: pair_alphabet pair append_scanned_simp)
  }
  thus ?thesis by (simp add: scan_def)
qed

corollary scan_nil_simp[simp]:
  "scan [] = ([], [])"
  by (simp add: scan_word_simp[of "[]", simplified])

corollary scan_last_var_simp[simp]:
  "scan (u @ [Inl x]) = scan u @@@ [(x, [])]"
  by (simp add: scan_last_simp[of "u" "x" "[]", simplified])

corollary scan_last_single_simp[simp]:
  "scan (Inl x # map Inr w) = ([], [(x, w)])"
  by (simp add: scan_last_simp[of "[]", simplified] append_scanned_simp)

corollary scan_var_simp[simp]: "scan [Inl x] = ([], [(x, [])])"
  by (simp add: scan_last_var_simp[of "[]" "x", simplified] append_scanned_simp)

lemma scan_pair_nil_simp[simp]: "scan_pair [] = []"
  unfolding scan_pair_def by simp

lemma scan_pair_var_simp[simp]: "scan_pair [Inl x] = [(x, [])]"
  unfolding scan_pair_def by simp

lemma scan_pair_alpha_simp[simp]: "scan_pair (Inr a#u) = scan_pair u"
  unfolding scan_pair_def scan_def
proof (simp)
  fix as bs
  show "snd (scan_head as u) = snd (scan_head bs u)"
    by (induct u arbitrary: as bs rule: xa_induct, simp_all)
qed

lemma scan_pair_word_simp[simp]: "scan_pair (map Inr as) = []"
  unfolding scan_pair_def by simp

lemma scan_pair_last_simp[simp]:
  "scan_pair (u @ Inl x # map Inr w) = scan_pair u @ [(x :: 'x, w)]"
  unfolding scan_pair_def
  by (cases "scan u", simp add: append_scanned_simp)

lemma snd_scan:
  "snd (scan u) = scan_pair u"
  unfolding scan_pair_def by simp

subsubsection \<open>Flat\<close>

text \<open>flatten pairs\<close>

fun flat_rec :: "('y, 'b) scanned_tail \<Rightarrow> ('y + 'b) list" where
  "flat_rec [] = []" |
  "flat_rec ((x, as)#xas) = Inl x # map Inr as @ flat_rec xas"

definition flat :: "('y, 'b) scanned \<Rightarrow> ('y + 'b) list" where
  "flat = (\<lambda>(b0, xas). map Inr b0 @ flat_rec xas)"

lemma flat_simp:
  "flat (b0, xas) = map Inr b0 @ flat_rec xas"
  unfolding flat_def by simp

lemma flat_rec_append[simp]: "flat_rec (xs @ ys) = flat_rec xs @ flat_rec ys"
  by (induct xs arbitrary: ys rule: pair_rev_induct, simp_all)

lemma flat_word_simp[simp]: "flat (w, []) = map Inr w"
  by (induct w, simp_all add: flat_def)

lemma flat_append[simp]: "flat (xas @@@ xs) = flat xas @ flat_rec xs"
proof (induct xas arbitrary: xs rule: scanned_rev_induct)
  case (Nil w)
  then show ?case by (simp add: append_scanned_simp flat_def)
next
  case (PairSnoc y bs sc)
  then show ?case by (simp add: append_scanned_simp append_scanned_assoc)
qed

theorem scan_inverse: "flat (scan u) = u"
  by (induct u rule: xw_induct, simp_all)


end
