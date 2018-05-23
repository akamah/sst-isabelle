(* Title:   Decompose_Update.thy
   Author:  Akama Hitoshi
*)

section \<open>Decomposition of an Update\<close>

theory Decompose_Update
  imports Main Update List SST
begin

(* an Update can be divided into two objects:
 * Shuffle (M\<^sup>1): shuffle and concatenate variables.
 * Store   (M\<^sup>2): stores strings which'll be concatenated to variables:
 *)

(* an detailed index of string in Append. 
 * (x, k) means the position of a k-th variable used in the assignment to x.
 *)
type_synonym 'y index = "'y \<times> nat"

(* Shuffle *)
type_synonym 'y shuffle = "'y \<Rightarrow> 'y list"

(* unit operation of Shuffle *)
definition idS :: "'y shuffle" where
  "idS \<equiv> (\<lambda>y. [y])"

(* Store *)
type_synonym ('y, 'b) store = "'y index \<Rightarrow> 'b list"


subsection \<open>Utility functions\<close>

(* extract only variables from var-alphabet list *)
fun extract_variables :: "('x + 'b) list \<Rightarrow> 'x list" where
  "extract_variables [] = []" |
  "extract_variables (Inl x#xs) = x # extract_variables xs" |
  "extract_variables (Inr a#xs) = extract_variables xs"


lemma [simp]: "extract_variables (u @ v) = extract_variables u @ extract_variables v"
  by (induct u arbitrary: v rule: xa_induct; simp_all)

lemma extract_variables_left_id[simp]: "extract_variables (map Inl u) = u"
  by (induct u, simp_all)

lemma extract_variables_right_ignore[simp]: "extract_variables (map Inr u) = []"
  by (induct u, simp_all)


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

fun append_scanned :: "('y, 'b) scanned \<Rightarrow> ('y, 'b) scanned_tail \<Rightarrow> ('y, 'b) scanned" (infixl "@@@" 80) where
  "append_scanned (w, xas) yas = (w, xas @ yas)"

lemma append_scanned_assoc: "(xas @@@ yas) @@@ zas = xas @@@ (yas @ zas)"
  by (cases xas, simp)

lemma append_scanned_Nil[simp]: "xas @@@ [] = xas" 
  by (cases xas, simp)


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
      by (induct u arbitrary: as rule: xa_induct, simp_all add: pair_alphabet pair)
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
  by (simp add: scan_last_simp[of "[]", simplified])


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

lemma flat_last_simp[simp]: "flat (w, xas @ [(x, as)]) = flat (w, xas) @ Inl x # map Inr as"
  by (induct xas rule: pair_rev_induct, simp_all add: flat_def)


subsubsection \<open>Padding\<close>

text \<open>replace strings with a special meta-variable\<close>

fun padding_rec :: "nat \<Rightarrow> 'x \<Rightarrow> ('x \<times> 'b list) list \<Rightarrow> ('x + 'x index) list" where
  "padding_rec n y [] = []" |
  "padding_rec n y ((x, _)#xs) = Inl x # Inr (y, n) # padding_rec (Suc n) y xs"

definition padding :: "'y \<Rightarrow> 'b list \<times> ('y \<times> 'b list) list \<Rightarrow> ('y + 'y index) list" where
  "padding y = (\<lambda>(a0, xs). Inr (y, 0) # padding_rec 1 y xs)"


lemma padding_word_simp[simp]: "padding y (w, []) = [Inr (y, 0)]"
  by (simp add: padding_def)

lemma padding_last_simp[simp]: "padding y (w, xas @ [(x, as)]) = padding y (w, xas) @ [Inl x, Inr (y, Suc (length xas))]"
proof -
  { fix n x as
    have "padding_rec n y (xas @ [(x, as)]) = padding_rec n y xas @ [Inl x, Inr (y, n + length xas)]"
      by (induct xas arbitrary: n rule: pair_induct, simp_all)
  }
  then show ?thesis
    by (simp add: padding_def)
qed

subsubsection \<open>Others\<close>

fun nth_string' where
  "nth_string' s [] k = s" |
  "nth_string' s ((x,as)#xas) 0 = as" |
  "nth_string' s  (_#xas) (Suc k) = nth_string' s xas k"


lemma nth_string'_append:
 "nth_string' s (xs @ ys) k
 = (if k < length xs then nth_string' s xs k 
                     else nth_string' s ys (k - length xs))"
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


fun nth_string'' where
  "nth_string'' s (w, xas) 0 = w" |
  "nth_string'' s (w, xas) (Suc n) = nth_string' s xas n"


definition flat_store where
  "flat_store d xas yi = (case yi of
    (Inl y) \<Rightarrow> [Inl y] |
    (Inr (x, k)) \<Rightarrow> map Inr (nth_string'' (d (x, k)) xas k))"

fun flat_store' where
  "flat_store' xs yi = flat_store (\<lambda>(x, k). []) xs yi"


lemma scan_inverse: "flat (scan u) = u"
  by (induct u rule: xw_induct,
      simp_all add: scan_word_simp flat_word_simp scan_last_simp flat_last_simp)


subsection \<open>Resolve\<close>
text \<open>\<pi> in the thesis\<close>

definition resolve_shuffle :: "('y, 'b) update \<Rightarrow> 'y shuffle" where
  "resolve_shuffle \<theta> y = extract_variables (\<theta> y)"

definition resolve_store :: "('y index \<Rightarrow> 'b list) \<Rightarrow> ('y, 'b) update \<Rightarrow> ('y, 'b) store" where
  "resolve_store d \<theta> yi = (case yi of (x, k) \<Rightarrow> nth_string'' (d (x, k)) (scan (\<theta> x)) k)"

(*
fun resolve_store' :: "('y, 'b) update \<Rightarrow> ('y, 'b) store" where
  "resolve_store' \<theta> y = resolve_store (\<lambda>(x, k). []) \<theta> y"
*)

subsection \<open>Synthesize\<close>
text \<open>inverse of \<pi> in the thesis\<close>

definition synthesize_shuffle :: "'y shuffle \<Rightarrow> ('y, 'y + 'y index, 'b) update'" where
  "synthesize_shuffle s y = map Inl (padding y (scan (map Inl (s y) :: ('y + 'y) list)))"

definition synthesize_store :: "('y, 'b) store \<Rightarrow> ('y + 'y index, 'y, 'b) update'" where
  "synthesize_store a yi = (case yi of
     (Inl y) \<Rightarrow> [Inl y] | 
     (Inr i) \<Rightarrow> map Inr (a i))"

lemma concat_map_synthesize_store_map_Inr:
  "concat (map (synthesize_store a) (map Inr w)) = map Inr (concat (map a w))"
  by (induct w, simp_all add: synthesize_store_def)

definition synthesize :: "'y shuffle \<times> ('y, 'b) store \<Rightarrow> ('y, 'b) update" where
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

lemma resolve_idU_empty: "resolve_store (\<lambda>x. []) idU (y, k) = (\<lambda>y'. []) (y, k)"
proof (cases k)
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
  

lemma padding_rec_scan_pair_ignore_alphabets_0:
      "padding_rec n x (scan_pair y0 as (map Inl (extract_variables u))) 
     = padding_rec n x (scan_pair y0 bs u)"
  by (induct u arbitrary: n y0 as bs rule: xa_induct, simp_all)

lemma padding_rec_scan_pair_ignore_alphabets:
      "padding_rec n x (scan_pair y0 as (map Inl (extract_variables u))) 
     = padding_rec n x (scan_pair y0 [] u)"
  by (simp only: padding_rec_scan_pair_ignore_alphabets_0)

lemma padding_scan_head_ignore_alphabet: "padding y (scan_head [a] xs) = padding y (scan_head [] xs)"
  by (induct xs rule: scan_head.induct, simp_all add: padding_def)

lemma padding_scan_ignore_alphabet: "padding x (scan (map Inl (extract_variables u))) = padding x (scan u)"
proof (induct u rule: xa_induct)
  case Nil
  then show ?case by (simp add: scan_def padding_def)
next
  case (Var y xs)
  then show ?case by (simp add: scan_def padding_rec_scan_pair_ignore_alphabets padding_def)
next
  case (Alpha a xs)
  then show ?case by (simp add: scan_def padding_scan_head_ignore_alphabet)
qed


lemma synthesize_resolve_eq_flat:
  assumes "yi = Inl y \<or> yi = Inr (x, k)"
  shows "synthesize_store (resolve_store d m) yi = flat_store d (scan (m x)) yi"
proof (cases yi)
  case (Inl a)
  then show ?thesis by (simp add: resolve_store_def synthesize_store_def flat_store_def)
next
  case (Inr b)
  then have "yi = Inr (x, k)" using assms by simp
  then show ?thesis
    by (simp add: resolve_store_def synthesize_store_def flat_store_def)
qed

lemma padding_rec_x: "list_all (\<lambda>yi. (\<exists>y. yi = Inl y) \<or> (\<exists>k. yi = Inr (x, k))) (padding_rec n x xas)"
  by (induct xas rule: padding_rec.induct, simp_all)

lemma padding_x: "list_all (\<lambda>yi. (\<exists>y. yi = Inl y) \<or> (\<exists>k. yi = Inr (x, k))) (padding x xas)"
  by (cases xas, simp add: padding_rec_x padding_def)

lemma concat_map_synthesize_resolve_flat:
  assumes "list_all (\<lambda>yi. (\<exists>y. yi = Inl y) \<or> (\<exists>k. yi = Inr (x, k))) xs"
  shows "concat (map (synthesize_store (resolve_store d m)) xs) = concat (map (flat_store d (scan (m x))) xs)"
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
  "concat (map (synthesize_store (resolve_store d m)) (padding x xas)) =
   concat (map (flat_store d (scan (m x))) (padding x xas))"
  by (rule concat_map_synthesize_resolve_flat, rule padding_x)


lemma flat_append[simp]: "flat (b0, xs @ ys) = flat (b0, xs) @ flat_rec ys"
proof (induct xs arbitrary: ys)
  case Nil
  then show ?case by (simp add: flat_def)
next
  case (Cons xas xs)
  then show ?case proof (cases xas)
    case (Pair x as)
    then show ?thesis by (simp add: flat_def)
  qed
qed


lemma flat_store_padding_append: 
      "concat (map (flat_store d (b0, xs @ ys)) (padding y (b0, xs @ ys)))
     = concat (map (flat_store d (b0, xs)) (padding y (b0, xs))) 
       @ concat (map (flat_store d (b0, xs @ ys)) 
                   (padding_rec (Suc (length xs)) y ys))"
proof (induct xs arbitrary: ys rule: rev_induct)
  case Nil
  then show ?case by (simp add: padding_def flat_store_def)
next
  case (snoc xas xs)
  show ?case proof (cases xas)
    case (Pair x as)
    then show ?thesis
      by (simp add: snoc, simp add: flat_store_def nth_string'_append)
  qed
qed

lemma flat_store_flat: "concat (map (flat_store d scanned) (padding x scanned)) = flat scanned"
proof -
  { fix b0 xs
    have "concat (map (flat_store d (b0, xs)) (padding x (b0, xs))) = flat (b0, xs)"
    proof (induct xs rule: pair_rev_induct)
      case Nil
      then show ?case by (simp add: flat_store_def padding_def flat_def)
    next
      case (PairSnoc y as xas) then show ?case
        apply (simp add: flat_store_padding_append)
        apply (simp add: flat_store_def nth_string'_append)
        done
    qed
  }
  then show ?thesis by (cases scanned, simp)
qed


theorem resolve_inverse: "synthesize (resolve_shuffle m, resolve_store d m) = m"
  by (auto simp add: comp_def synthesize_shuffle_def hat_hom_left_concat_map resolve_shuffle_def
                     padding_scan_ignore_alphabet concat_map_padding flat_store_flat scan_inverse
                     synthesize_def)


lemma extract_variables_synthesize_store: "extract_variables (concat (map (synthesize_store a) u)) = extract_variables u"
  by (induct u rule: xa_induct, simp_all add: synthesize_store_def)

lemma extract_variables_padding_scan: "extract_variables (padding x (scan (map Inl u))) = u"
proof (induct u rule: rev_induct)
  case Nil
  then show ?case by (simp add: scan_def padding_def synthesize_store_def)
next
  case (snoc x xs)
  then show ?case by (simp add: scan_last_var_simp padding_last_simp)
qed


theorem synthesize_inverse_shuffle: "resolve_shuffle (synthesize (s, a)) = s"
  apply (rule ext)
  apply (simp add: synthesize_def resolve_shuffle_def comp_def synthesize_shuffle_def hat_hom_left_concat_map)
  apply (simp add: extract_variables_synthesize_store extract_variables_padding_scan)
  done


subsection \<open>Example\<close>

definition poyo :: "(int, char) update" where
  "poyo = (%z. if z = 0 then [Inr (CHR ''P''), Inl 0, Inr (CHR ''Q''), Inl 0, Inr (CHR ''R'')]
        else if z = 1 then [Inr (CHR ''A''), Inl 0, Inr (CHR ''B''), Inl 1, Inr (CHR ''C'')]
        else [])"

declare poyo_def [simp]

value "poyo 1"
value "resolve_store (\<lambda>_. ''NOT FOUND'') poyo (0, 2)"

lemma "resolve_shuffle poyo 0 = [0, 0]" by (simp add: resolve_shuffle_def)
lemma "resolve_shuffle poyo 1 = [0, 1]" by (simp add: resolve_shuffle_def)

lemma "resolve_store f poyo (0, 0) = ''P''" by (simp add: resolve_store_def scan_def)
lemma "resolve_store f poyo (0, 1) = ''Q''" by (simp add: resolve_store_def scan_def)
lemma "resolve_store f poyo (1, 0) = ''A''" by (simp add: resolve_store_def scan_def)
lemma "resolve_store f poyo (1, 1) = ''B''" by (simp add: resolve_store_def scan_def)




end
