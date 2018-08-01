(* Title:   Decompose_Update.thy
   Author:  Akama Hitoshi
*)

section \<open>Decomposition of an Update\<close>

theory Decompose_Update
  imports Main Enum Update List SST
begin

(* an Update can be divided into two objects:
 * Shuffle (M\<^sup>1): shuffle and concatenate variables.
 * Store   (M\<^sup>2): stores strings which'll be concatenated to variables:
 *)

(* an detailed index of string in Append. 
 * (x, k) means the position of a k-th variable used in the assignment to x.
 *)
type_synonym ('y, 'i) index = "'y \<times> 'i"

(* Shuffle *)
type_synonym 'y shuffle = "'y \<Rightarrow> 'y list"

(* unit operation of Shuffle *)
definition idS :: "'y shuffle" where
  "idS \<equiv> (\<lambda>y. [y])"

(* Store *)
type_synonym ('y, 'i, 'b) store = "('y, 'i) index \<Rightarrow> 'b list"


subsection \<open>Utility functions\<close>

fun enum_to_nat' :: "'e list \<Rightarrow> 'e \<Rightarrow> nat" where
  "enum_to_nat' [] e = undefined" |
  "enum_to_nat' (x#xs) e = (if x = e then 0 else 1 + enum_to_nat' xs e)"

fun nat_to_enum' :: "'e list \<Rightarrow> nat \<Rightarrow> 'e" where
  "nat_to_enum' [] n = undefined" |
  "nat_to_enum' (x#xs) 0 = x" |
  "nat_to_enum' (x#xs) (Suc n) = nat_to_enum' xs n"

definition enum_to_nat :: "'e::enum \<Rightarrow> nat" where
  "enum_to_nat e = enum_to_nat' Enum.enum e"

definition nat_to_enum :: "nat \<Rightarrow> 'e::enum" where
  "nat_to_enum n = nat_to_enum' Enum.enum n"

lemma nat_to_enum'_in:
  assumes "n < length xs"
  shows "nat_to_enum' xs n \<in> set xs"
using assms by (induct xs n rule: nat_to_enum'.induct, simp_all)


lemma list_nat_iso:
  assumes "e \<in> set xs"
  shows "nat_to_enum' xs (enum_to_nat' xs e) = e"
  unfolding enum_to_nat_def
using assms by (induct xs arbitrary: e, auto)

lemma enum_nat_iso:
  assumes "e \<in> set Enum.enum"
  shows "nat_to_enum (enum_to_nat e) = e"
  unfolding nat_to_enum_def enum_to_nat_def
  by (rule list_nat_iso, rule assms(1))

lemma nat_list_iso:
  assumes "n < length xs"
  assumes "distinct xs"
  shows "enum_to_nat' xs (nat_to_enum' xs n) = n"
using assms proof (induct xs n rule: nat_to_enum'.induct)
  case (1 n)
  then show ?case by simp
next
  case (2 x xs)
  then show ?case by simp
next
  case (3 x xs n)
  then show ?case proof (simp)
    have "n < length xs"
      using "3.prems"(1) by auto
    moreover have "distinct xs"
      using "3.prems"(2) by auto
    moreover have "enum_to_nat' xs (nat_to_enum' xs n) = n"
      by (simp add: "3.hyps" calculation(1) calculation(2))
    moreover have "nat_to_enum' xs n \<in> set xs"
      by (simp add: calculation(1) nat_to_enum'_in)
    ultimately show "x \<noteq> nat_to_enum' xs n"
      using "3.prems"(2) by auto
  qed
qed

lemma nat_enum_iso:
  assumes "n < length (Enum.enum :: ('e::enum) list)"
  shows "enum_to_nat (nat_to_enum n :: 'e) = n"
  unfolding enum_to_nat_def nat_to_enum_def
  by (rule nat_list_iso, rule assms(1), rule Enum.enum_distinct)

subsubsection \<open>Induction on list of pairs\<close>

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

text \<open>first string and pairs of a variable and a string\<close>

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

fun scan_pair :: "'y \<Rightarrow> 'b list \<Rightarrow> ('y + 'b) list \<Rightarrow> ('y, 'b) scanned_tail" where
  "scan_pair x as [] = [(x, as)]" |
  "scan_pair x as (Inl y#u) = (x, as) # scan_pair y [] u" |
  "scan_pair x as (Inr a#u) = scan_pair x (as @ [a]) u"

fun scan_head :: "'b list \<Rightarrow> ('y + 'b) list \<Rightarrow> ('y, 'b) scanned" where
  "scan_head as [] = (as, [])" |
  "scan_head as (Inl x#u) = (as, scan_pair x [] u)" |
  "scan_head as (Inr a#u) = scan_head (as @ [a]) u"

definition scan :: "('y + 'b) list \<Rightarrow> ('y, 'b) scanned" where
  "scan u = scan_head [] u"

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
    have "scan_pair y bs (map Inr w) = [(y, bs @ w)]" by (induct w arbitrary: bs, simp_all)
  } note pair_alphabet = this
  { fix x y :: 'x and as u
    have "scan_pair x as (u @ Inl y # map Inr w) = scan_pair x as u @ [(y, w)]"
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


subsubsection \<open>Flat\<close>

text \<open>flatten pairs\<close>

fun flat_rec where
  "flat_rec [] = []" |
  "flat_rec ((x, as)#xas) = Inl x # map Inr as @ flat_rec xas"

definition flat where
  "flat = (\<lambda>(b0, xas). map Inr b0 @ flat_rec xas)"


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



subsubsection \<open>Padding\<close>

text \<open>replace strings with a special meta-variable\<close>

type_synonym ('y, 'i) pad = "('y + ('y, 'i) index) list"


fun padding_rec :: "nat \<Rightarrow> 'y \<Rightarrow> ('y, 'b) scanned_tail \<Rightarrow> ('y, 'i::enum) pad" where
  "padding_rec n y [] = []" |
  "padding_rec n y ((x, _)#xs) = Inl x # Inr (y, nat_to_enum n) # padding_rec (Suc n) y xs"

fun padding :: "'y \<Rightarrow> ('y, 'b) scanned \<Rightarrow> ('y, 'i::enum) pad" where
  "padding y (a0, xs) = Inr (y, nat_to_enum 0) # padding_rec 1 y xs"

lemma padding_rec_append[simp]:
  "padding_rec n y (xs @ ys) = padding_rec n y xs @ padding_rec (n + length xs) y ys"
proof (induct xs arbitrary: ys n rule: pair_induct)
  case Nil
  then show ?case by simp
next
  case (PairCons x as xas)
  then show ?case by (cases n, simp_all)
qed


lemma padding_word_simp[simp]: 
  "padding y (w, []) = [Inr (y, nat_to_enum 0)]"
  by (simp)

lemma padding_last_simp[simp]: 
  "padding y (xas @@@ [(x, as :: 'b list)])
 = padding y xas @ [Inl x, Inr (y, nat_to_enum (length_scanned xas))]"
proof -
  { fix n x yas and as :: "'b list"
    have "padding_rec n y (yas @ [(x, as)]) = padding_rec n y yas @ [Inl x, Inr (y, nat_to_enum (n + length yas))]"
      by (induct yas arbitrary: n rule: pair_induct, simp_all)
  } note that = this
  then show ?thesis by (cases xas, simp add: that append_scanned_simp)
qed

lemma padding_append_scanned:
  "padding y (xas @@@ ys) = padding y xas @ padding_rec (length_scanned xas) y ys"
proof (induct ys arbitrary: xas rule: pair_rev_induct)
  case Nil 
  then show ?case by (simp add: append_scanned_simp)
next
  case (PairSnoc x as sc)
  then show ?case by (simp add: append_scanned_assoc[symmetric])
qed


subsubsection \<open>nth_string\<close>

fun nth_string' where
  "nth_string' [] k = []" |
  "nth_string' ((x,as)#xas) 0 = as" |
  "nth_string' (_#xas) (Suc k) = nth_string' xas k"

lemma nth_string'_append:
 "nth_string' (xs @ ys) k
 = (if k < length xs then nth_string' xs k 
                     else nth_string' ys (k - length xs))"
proof (induct xs arbitrary: k rule: pair_induct)
  case Nil
  then show ?case by simp
next
  case (PairCons x as xas)
  then show ?case proof (cases k)
    case 0
    then show ?thesis by simp
  next
    case (Suc nat)
    then show ?thesis by (simp add: PairCons)
  qed
qed

lemma nth_string'_length: "nth_string' (xs @ ys) (length xs) = nth_string' ys 0" 
  by (induct xs rule: pair_induct, simp_all)


fun nth_string where
  "nth_string (w, xas) 0 = w" |
  "nth_string (w, []) (Suc n) = []" |
  "nth_string (w, (x, as) # xas) (Suc n) = nth_string (as, xas) n"


lemma nth_string_eq: "nth_string (w, xas) (Suc n) = nth_string' xas n"
proof (induct xas arbitrary: n w rule: pair_induct)
  case Nil
  then show ?case by simp
next
  case (PairCons x as xas)
  then show ?case proof (cases n)
    case 0
    then show ?thesis by simp
  next
    case (Suc nat)
    then show ?thesis by (simp add: PairCons)
  qed
qed

lemma nth_string'_pos: "0 < n \<Longrightarrow> nth_string' ((x, as) # xas) n = nth_string' xas (n - 1)"
  by (auto simp add: Nat.gr0_conv_Suc)

lemma nth_string_Nil: "nth_string (w, []) n = (if n = 0 then w else [])"
  by (cases n, simp_all)

lemma nth_string_length: "nth_string (xas @@@ ys) (length_scanned xas) = nth_string' ys 0" 
proof (induct xas rule: scanned_induct)
case (Nil w)
  then show ?case by (simp add: append_scanned_simp nth_string_eq)
next
  case (PairCons x as sc)
  then show ?case by (simp add: append_scanned_simp nth_string_eq)
qed

lemma nth_string_pos: "0 < n \<Longrightarrow> nth_string (w, (x, as) # xas) n = nth_string (as, xas) (n - 1)"
  by (auto simp add: Nat.gr0_conv_Suc)

lemma nth_string_pos_Nil: "0 < n \<Longrightarrow> nth_string (w, []) n = []"
  by (auto simp add: Nat.gr0_conv_Suc)

lemma nth_string_pos': "0 < n \<Longrightarrow> nth_string (w, xas) n = nth_string' xas (n - 1)"
  by (auto simp add: Nat.gr0_conv_Suc nth_string_eq)


lemma nth_string_append: 
  "nth_string (xas @@@ ys) n 
 = (if n < length_scanned xas then nth_string xas n
                              else nth_string' ys (n - length_scanned xas))"
proof (induct xas arbitrary: n rule: scanned_induct)
  case Nil
  then show ?case by (auto simp add: append_scanned_simp nth_string_pos')
next
  case (PairCons w x as xas)
  then show ?case by (cases n, simp_all add: append_scanned_simp)
qed


lemma nth_string_append_last:
  "nth_string (xas @@@ [(x, as)]) n
 = (if n = length_scanned xas then as else nth_string xas n)"
proof (induct xas arbitrary: n rule: scanned_induct)
  case (Nil w)
  then show ?case proof (cases n)
    case 0
    then show ?thesis by (simp add: append_scanned_simp)
  next
    case (Suc k)
    then show ?thesis by (simp add: append_scanned_simp nth_string_pos_Nil)
  qed
next
  case (PairCons w x as xas)
  then show ?case proof (cases n)
    case 0
    then show ?thesis by (simp add: append_scanned_simp)
  next
    case (Suc k)
    then show ?thesis using PairCons by (simp add: append_scanned_simp)
  qed
qed

lemma nth_string_append_first:
  "nth_string (xas @@@ ys) 0 = nth_string xas 0"
  by (cases xas, simp add: append_scanned_simp)

corollary nth_string_lt_length:
  assumes "n < length_scanned sc"
  shows "nth_string (sc @@@ rest) n = nth_string sc n"
  using assms by (simp add: nth_string_append)


definition flat_store where
  "flat_store xas yi = (case yi of
    (Inl y) \<Rightarrow> [Inl y] |
    (Inr (x, i)) \<Rightarrow> map Inr (nth_string xas (enum_to_nat i)))"

lemma [simp]: "flat_store xas (Inl y) = [Inl y]" by (simp add: flat_store_def)

lemma [simp]:
  assumes "length_scanned sc < length (Enum.enum :: ('e::enum) list)"
  shows  "flat_store (sc @@@ [(x, as)]) (Inr (y, nat_to_enum (length_scanned sc) :: 'e)) = map Inr as"
using assms proof (induct sc rule: scanned_induct)
  case (Nil w)
  then show ?case by (simp add: flat_store_def append_scanned_simp nat_enum_iso)
next
  case (PairCons w x as xas)
  then show ?case 
    by (simp add: flat_store_def append_scanned_simp  nth_string_eq nth_string'_length nat_enum_iso)
qed


theorem scan_inverse: "flat (scan u) = u"
  by (induct u rule: xw_induct, simp_all)


subsection \<open>Resolve\<close>
text \<open>\<pi> in the thesis\<close>

definition resolve_shuffle :: "('y, 'b) update \<Rightarrow> 'y shuffle" where
  "resolve_shuffle \<theta> y = extract_variables (\<theta> y)"

definition resolve_store :: "('y, 'b) update \<Rightarrow> ('y, 'i::enum, 'b) store" where
  "resolve_store \<theta> yi = (case yi of (x, k) \<Rightarrow> nth_string (scan (\<theta> x)) (enum_to_nat k))"


subsection \<open>Synthesize\<close>
text \<open>inverse of \<pi> in the thesis\<close>

definition synthesize_shuffle :: "'y shuffle \<Rightarrow> ('y, 'y + ('y, 'i::enum) index, 'b) update'" where
  "synthesize_shuffle s y = map Inl (padding y (scan (map Inl (s y) :: ('y + 'y) list)))"

definition synthesize_store :: "('y, 'i::enum, 'b) store \<Rightarrow> ('y + ('y, 'i) index, 'y, 'b) update'" where
  "synthesize_store a yi = (case yi of
     (Inl y) \<Rightarrow> [Inl y] | 
     (Inr i) \<Rightarrow> map Inr (a i))"

lemma concat_map_synthesize_store_map_Inr:
  "concat (map (synthesize_store a) (map Inr w)) = map Inr (concat (map a w))"
  by (induct w, simp_all add: synthesize_store_def)

definition synthesize :: "'y shuffle \<times> ('y, 'i::enum, 'b) store \<Rightarrow> ('y, 'b) update" where
  "synthesize sa = (case sa of (s, a) \<Rightarrow> synthesize_store a \<bullet> synthesize_shuffle s)"


subsection \<open>Properties of Decomposition\<close>


lemma map_alpha_synthesize_shuffle: "t \<star> synthesize_shuffle s = synthesize_shuffle s"
  by (auto simp add: map_alpha_def hat_alpha_left_ignore synthesize_shuffle_def)

lemma map_alpha_synthesize_store: "t \<star> synthesize_store p = synthesize_store (concat o map t o p)"
  by (rule ext_sum, simp_all add: map_alpha_def Update.hat_alpha_right_map synthesize_store_def)

lemma map_alpha_synthesize: "t \<star> synthesize (s, a) = synthesize (s, concat o map t o a)"
  by (auto simp add: map_alpha_distrib map_alpha_synthesize_shuffle map_alpha_synthesize_store synthesize_def)


lemma resolve_idU_idS: "resolve_shuffle idU = idS"
  by (auto simp add: idU_def idS_def resolve_shuffle_def)

lemma resolve_idU_empty: "resolve_store idU (y, k) = (\<lambda>y'. []) (y, k)"
proof (cases "enum_to_nat k")
  case 0
  then show ?thesis by (simp add: resolve_store_def idU_def scan_def)
next
  case (Suc n)
  then show ?thesis by (cases n, simp_all add: resolve_store_def idU_def scan_def)
qed


lemma resolve_shuffle_distrib_str: 
  "extract_variables (hat_hom \<phi> u) = concat (map (resolve_shuffle \<phi>) (extract_variables u))"
  by (induct u rule: xa_induct, simp_all add: resolve_shuffle_def)

lemma resolve_shuffle_distrib: "resolve_shuffle (\<phi> \<bullet> \<psi>) = concat o map (resolve_shuffle \<phi>) o resolve_shuffle \<psi>"
  by (rule ext, simp add: comp_def resolve_shuffle_def resolve_shuffle_distrib_str)


lemma length_scanned_ignore_alphabet: 
  "length_scanned (scan (map Inl (extract_variables u))) = length_scanned (scan u)"
  by (induct u rule: xw_induct, simp_all)

lemma padding_scan_ignore_alphabet:
  "padding x (scan (map Inl (extract_variables u))) = padding x (scan u)"
  by (induct u rule: xw_induct, auto simp add: length_scanned_ignore_alphabet)

lemma synthesize_resolve_eq_flat:
  assumes "yi = Inl y \<or> yi = Inr (x, k::('e::enum))"
  shows "synthesize_store (resolve_store m) yi = flat_store (scan (m x)) yi"
proof (cases "yi")
  case (Inl a)
  then show ?thesis by (simp add: resolve_store_def synthesize_store_def flat_store_def)
next
  case (Inr b)
  then have "yi = Inr (x, k)" using assms by simp
  then show ?thesis
    by (simp add: resolve_store_def synthesize_store_def flat_store_def)
qed

subsection \<open>Properties of flat_store and synthesize_store & resolve_store\<close>

abbreviation z_equal_var where
  "z_equal_var x yi \<equiv> ((\<exists>y. yi = Inl y) \<or> (\<exists>k. yi = Inr (x, k)))"


lemma padding_x: "list_all (z_equal_var x) (padding x xas)"
  by (induct xas rule: scanned_rev_induct, simp_all)

lemma concat_map_synthesize_resolve_flat:
  assumes "list_all (z_equal_var x) xs"
  shows "concat (map (synthesize_store (resolve_store m)) xs) = concat (map (flat_store (scan (m x))) xs)"
using assms proof (induct xs rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x u)
  then show ?case by (simp add: synthesize_resolve_eq_flat)
next
  case (Alpha a u)
  then show ?case using synthesize_resolve_eq_flat by force
qed

  
lemma concat_map_padding:
  "concat (map (synthesize_store (resolve_store m)) (padding x xas :: ('y, 'i::enum) pad)) =
   concat (map (flat_store (scan (m x))) (padding x xas :: ('y, 'i) pad))"
  by (rule concat_map_synthesize_resolve_flat, rule padding_x)


abbreviation z_less_than where
  "z_less_than n z \<equiv> (\<forall>y i. z = Inr (y, i) \<longrightarrow> enum_to_nat i < n)"

lemma z_less_than_Suc: "z_less_than n z \<Longrightarrow> z_less_than (Suc n) z"
  by (simp add: less_SucI)

lemma all_z_less_than_Suc:
  assumes "list_all (z_less_than n) xs"
  shows "list_all (z_less_than (Suc n)) xs"
  using assms by (induct xs, simp_all add: less_SucI)

lemma flat_store_lt_length:
  assumes "z_less_than (length_scanned sc) (Inr (y, i))"
  shows "flat_store (sc @@@ rest) (Inr (y, i)) = flat_store sc (Inr (y, i))"
  using assms unfolding flat_store_def by (simp add: nth_string_lt_length)

lemma cm_flat_store_ignore_rest:
  assumes "list_all (z_less_than (length_scanned sc)) us"
  shows "concat (map (flat_store (sc @@@ rest)) us) = concat (map (flat_store sc) us)"
using assms proof (induct us rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case by simp
next
  case (Alpha a xs)
  have "z_less_than (length_scanned sc) (Inr a)" using Alpha.prems by auto
  moreover have "list_all (z_less_than (length_scanned sc)) xs" using Alpha.prems by auto
  ultimately show ?case by (cases a, simp add: flat_store_lt_length Alpha)
qed

lemma padding_lt_length_scanned:
  assumes "length_scanned sc \<le> length (Enum.enum :: 'i list)"
  shows "list_all (z_less_than (length_scanned sc)) (padding x sc :: ('y, 'i::enum) pad)"
using assms proof (induct sc rule: scanned_rev_induct)
  case (Nil w)
  then show ?case proof (simp)
    assume "Suc 0 \<le> length (Enum.enum :: 'i list)"
    then have "0 < length (Enum.enum :: 'i list)"
      by (simp add: less_eq_Suc_le)
    then show "enum_to_nat (nat_to_enum 0 :: 'i) = 0"
      by (simp add: nat_enum_iso)
  qed
next
  case (PairSnoc x as sc)
  then show ?case proof (simp add: all_z_less_than_Suc)
    assume "Suc (length_scanned sc) \<le> length (Enum.enum :: 'i list)"
    then have "length_scanned sc < length (Enum.enum :: 'i list)" by simp
    then show "enum_to_nat (nat_to_enum (length_scanned sc) :: 'i) < Suc (length_scanned sc)"
      by (simp add: nat_enum_iso)
  qed
qed


lemma cm_flat_store_padding_ignore:
  assumes "length_scanned sc \<le> length (Enum.enum :: ('i::enum) list)"
  shows "concat (map (flat_store (sc @@@ rest)) (padding x sc :: ('y, 'i) pad)) 
       = concat (map (flat_store sc) (padding x sc :: ('y, 'i) pad))"
proof -
  have "list_all (z_less_than (length_scanned sc)) (padding x sc :: ('y, 'i) pad)"
    using assms by (simp add: padding_lt_length_scanned)
  then show ?thesis by (simp add: cm_flat_store_ignore_rest)
qed

lemma flat_store_flat:
  assumes "length_scanned sc \<le> length (Enum.enum :: ('i::enum) list)"
  shows "concat (map (flat_store sc) (padding x sc :: ('y, 'i) pad)) = flat sc"
using assms proof (induct sc rule: scanned_rev_induct)
  case (Nil w)
  then have "0 < length (Enum.enum :: 'i list)"
    by auto
  then show ?case using assms by (simp add: flat_store_def nat_enum_iso)
next
  case (PairSnoc x as sc)
  then show ?case by (simp add: cm_flat_store_padding_ignore)
qed


lemma bounded_copy_length_scanned:
  assumes "bounded_copy k m"
  shows "length_scanned (scan (m x)) \<le> k * k"
  oops 


theorem resolve_inverse: "synthesize (resolve_shuffle m, resolve_store m :: ('y, 'i::enum, 'b) store) = m"
  apply (rule ext)
  apply (simp add: synthesize_def synthesize_shuffle_def comp_def)
  apply (simp add: resolve_shuffle_def)
  apply (simp add: hat_hom_left_concat_map padding_scan_ignore_alphabet)
  apply (simp add: concat_map_padding flat_store_flat scan_inverse)
  oops

lemma extract_variables_synthesize_store: "extract_variables (concat (map (synthesize_store a) u)) = extract_variables u"
  by (induct u rule: xa_induct, simp_all add: synthesize_store_def)

lemma extract_variables_padding_scan: "extract_variables (padding x (scan (map Inl u))) = u"
proof (induct u rule: rev_induct)
  case Nil
  then show ?case by (simp add: scan_def synthesize_store_def)
next
  case (snoc x xs)
  then show ?case by (simp add: )
qed


theorem synthesize_inverse_shuffle: "resolve_shuffle (synthesize (s, a)) = s"
  apply (rule ext)
  apply (simp add: synthesize_def resolve_shuffle_def comp_def synthesize_shuffle_def hat_hom_left_concat_map
                   extract_variables_synthesize_store extract_variables_padding_scan)
  done


subsection \<open>Example\<close>

definition poyo :: "(int, char) update" where
  "poyo = (%z. if z = 0 then [Inr (CHR ''P''), Inl 0, Inr (CHR ''Q''), Inl 0, Inr (CHR ''R'')]
        else if z = 1 then [Inr (CHR ''A''), Inl 0, Inr (CHR ''B''), Inl 1, Inr (CHR ''C'')]
        else [])"

declare poyo_def [simp]

value "poyo 1"
value "resolve_store poyo (0, False)"

lemma "resolve_shuffle poyo 0 = [0, 0]" by (simp add: resolve_shuffle_def)
lemma "resolve_shuffle poyo 1 = [0, 1]" by (simp add: resolve_shuffle_def)

(*
lemma "resolve_store poyo (0, False) = ''P''" apply (auto simp add: resolve_store_def scan_def enum_to_nat_def)
lemma "resolve_store poyo (0, 1) = ''Q''" by (simp add: resolve_store_def scan_def)
lemma "resolve_store poyo (1, 0) = ''A''" by (simp add: resolve_store_def scan_def)
lemma "resolve_store poyo (1, 1) = ''B''" by (simp add: resolve_store_def scan_def)
*)



end
