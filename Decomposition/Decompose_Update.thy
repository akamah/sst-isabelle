(* Title:   Decompose_Update.thy
   Author:  Akama Hitoshi
*)

section \<open>Decomposition of an Update\<close>

theory Decompose_Update
  imports Main HOL.Enum HOL.List "../Util/Enum_Nat" "../Core/Update" "../Core/SST" "../Single_Use/Single_Use"
begin

(* an Update can be divided into two objects:
 * Shuffle (M\<^sup>1): shuffle and concatenate variables.
 * Store   (M\<^sup>2): stores strings which'll be concatenated to variables:
 *)

(* This is a type of max scanned length given bounded count 'k.
 * if 'k is instance of enum class, this type represents type-level natural number
 * |'k| + 1
 *)

(* an index of string in Store.
 * (y, k) means the position of a k-th variable used in the assignment to y.
 *)
type_synonym ('y, 'k) index = "'y \<times> 'k option"

(* Shuffle *)
type_synonym 'y shuffle = "'y \<Rightarrow> 'y list"


(* Store object is an array of string indexed with ('y, 'i) index *)
type_synonym ('y, 'i, 'b) store = "('y, 'i) index \<Rightarrow> 'b list"


subsection \<open>Utility functions\<close>

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

text \<open>Scanned string, w_0 y_1 w_1 y_2 w_2 ... y_n w_n\<close>
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

definition extract_variables_pair :: "('y \<times> 'b list) list \<Rightarrow> 'y list" where
  "extract_variables_pair ps = map fst ps"

lemma extract_variables_pair_Nil[simp]: "extract_variables_pair [] = []" 
  unfolding extract_variables_pair_def by simp

lemma extract_variables_pair_Cons[simp]: "extract_variables_pair ((x, as)#xas) = x # extract_variables_pair xas"
  unfolding extract_variables_pair_def by simp

lemma extract_variables_pair_snoc[simp]: "extract_variables_pair (xas @ [(x, as)]) = extract_variables_pair xas @ [x]"
  unfolding extract_variables_pair_def by simp



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

lemma length_scanned_hat_alpha: "length_scanned (scan (hat_alpha t u)) = length_scanned (scan u)"
  by (induct u rule: xw_induct, simp_all)

lemma length_scanned_ignore_alphabet: 
  "length_scanned (scan (map Inl (extract_variables u))) = length_scanned (scan u)"
  by (induct u rule: xw_induct, simp_all)


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

theorem scan_inverse: "flat (scan u) = u"
  by (induct u rule: xw_induct, simp_all)

subsection \<open>Resolve\<close>

text \<open>\<pi> in the thesis\<close>



definition resolve_shuffle :: "('y, 'b) update \<Rightarrow> 'y shuffle" where
  "resolve_shuffle \<theta> y = extract_variables (\<theta> y)"

abbreviation orElse where
  "orElse a b \<equiv> combine_options (\<lambda>x y. x) a b"

lemma orElse_assoc: "orElse (orElse a b) c = orElse a (orElse b c)"
proof (cases a)
  case None
  then show ?thesis by simp
next
  case A: (Some a)
  then show ?thesis proof (cases b)
    case None
    then show ?thesis by simp
  next
    case B: (Some b)
    then show ?thesis proof (cases c)
      case None
      then show ?thesis by simp
    next
      case C: (Some c)
      then show ?thesis by (simp add: A B C)
    qed
  qed
qed


fun counter0 :: "'x \<Rightarrow> nat" where
  "counter0 y = 0"

fun incr :: "('x \<Rightarrow> nat) \<Rightarrow> 'x \<Rightarrow> ('x \<Rightarrow> nat)" where
  "incr counter x x' = (if x' = x then Suc (counter x) else counter x')"

(* increment a counter by all elements of a row *)
definition incr_row :: "('x \<Rightarrow> nat) \<Rightarrow> 'x list \<Rightarrow> ('x \<Rightarrow> nat)" where
  "incr_row c xs = foldl incr c xs"

lemma [simp]: "incr_row c [] = c" unfolding incr_row_def by simp
lemma [simp]: "incr_row c (x#xs) = incr_row (incr c x) xs" unfolding incr_row_def by simp
lemma [simp]: "incr_row c (xs @ [x]) = incr (incr_row c xs) x"
  by (induct xs arbitrary: c, simp_all)
(*
fun incr_rows_until :: "('y \<Rightarrow> 'x list) \<Rightarrow> 'y \<Rightarrow> ('x \<Rightarrow> nat) \<Rightarrow> 'y list \<Rightarrow> ('x \<Rightarrow> nat)" where
  "incr_rows_until s y0 c Nil = c" |
  "incr_rows_until s y0 c (y#ys) =
    (if y = y0 then c else incr_rows_until s y0 (incr_row c (s y)) ys)"
*)


lemma incr_row_count_list: "incr_row c xs x = c x + count_list xs x"
  by (induct xs arbitrary: c, simp_all)

fun take_rows_until :: "'y \<Rightarrow> 'y list \<Rightarrow> 'y list" where
  "take_rows_until y0 ys = takeWhile (not_equal y0) ys"

fun countup_rows :: "('y \<Rightarrow> 'x list) \<Rightarrow> ('x \<Rightarrow> nat) \<Rightarrow> 'y list \<Rightarrow> ('x \<Rightarrow> nat)" where
  "countup_rows s c0 ys = foldl (\<lambda>c y. incr_row c (s y)) c0 ys"

fun countup_rows_until :: "('y \<Rightarrow> 'x list) \<Rightarrow> 'y \<Rightarrow> 'y list \<Rightarrow> ('x \<Rightarrow> nat)" where
  "countup_rows_until s y0 ys = countup_rows s counter0 (take_rows_until y0 ys)"

lemma incr_rows_until_last:
  shows "countup_rows_until s y0 (ys @ [y]) =
           (if y0 \<in> set (ys @ [y]) then countup_rows_until s y0 ys
            else incr_row (countup_rows_until s y0 ys) (s y))" oops

(* lookup a single row *)
fun lookup_row :: "'x \<Rightarrow> nat \<Rightarrow> ('x \<Rightarrow> nat) \<Rightarrow> ('x \<times> 'a list) list \<Rightarrow> 'a list option" where
  "lookup_row x0 i0 c Nil           = None" |
  "lookup_row x0 i0 c ((x, as)#xas) =
    (if x = x0 \<and>  (c x) = i0 then Some as else lookup_row x0 i0 (incr c x) xas)"

fun lookup_rec where
  "lookup_rec m y0 i0 whole Nil    = None" |
  "lookup_rec m y0 i0 whole (y#ys) = 
     orElse (lookup_row y0 i0 (countup_rows_until (resolve_shuffle m) y0 whole) (scan_pair (m y)))
            (lookup_rec m y0 i0 whole ys)"

lemma lookup_rec_last:
  "lookup_rec m y0 i0 whole (ys @ [y]) =
    orElse (lookup_rec m y0 i0 whole ys)
           (lookup_row y0 i0 (countup_rows_until (resolve_shuffle m) y0 whole) (scan_pair (m y)))"
proof (induct ys)
case Nil
  then show ?case by simp
next
  case (Cons a ys)
  then show ?case by (simp add: orElse_assoc)
qed

(* lookup a string at specified position in a given update monoid *)
fun lookup :: "'y list \<Rightarrow> ('y, 'b) update \<Rightarrow> 'y \<Rightarrow> nat \<Rightarrow> 'b list" where
  "lookup ys m y i = (case lookup_rec m y i ys ys of
                       Some as \<Rightarrow> as |
                       None    \<Rightarrow> [])"

fun resolve_store_nat :: "('y::enum, 'b) update \<Rightarrow> ('y, nat, 'b) store" where  
  "resolve_store_nat m (y, None) = fst (scan (m y))" |
  "resolve_store_nat m (y, Some n) = lookup (Enum.enum :: 'y list) m y n"

definition resolve_store :: "'k::enum boundedness \<Rightarrow> ('y::enum, 'b) update \<Rightarrow> ('y, 'k::enum, 'b) store" where  
  "resolve_store B m yi = (case yi of
     (y, None)   \<Rightarrow> resolve_store_nat m (y, None) | 
     (y, Some k) \<Rightarrow> resolve_store_nat m (y, Some (enum_to_nat k)))"

fun empty_store :: "('y::enum, 'k, 'b) store" where
  "empty_store (y, k) = []"


subsection \<open>Synthesize\<close>
text \<open>inverse of \<pi> in the thesis\<close>

fun give_index_row_rec :: "('x \<Rightarrow> nat) \<Rightarrow> 'x list \<Rightarrow> ('x + 'x \<times> nat option) list" where
  "give_index_row_rec _ Nil    = []" |
  "give_index_row_rec c (x#xs) = Inl x # Inr (x, Some ( (c x))) # give_index_row_rec (incr c x) xs"

lemma [simp]: "give_index_row_rec c (xs @ [x]) 
     = give_index_row_rec c xs @ [Inl x, Inr (x, Some (incr_row c xs x))]"
proof (induct xs arbitrary: c)
  case Nil
  then show ?case by simp
next
  case (Cons x' xs)
  then show ?case by (cases "x' = x", simp_all del: incr.simps)
qed

fun give_index_row :: "'y \<Rightarrow> ('y \<Rightarrow> nat) \<Rightarrow> 'y list \<Rightarrow> ('y + 'y \<times> nat option) list" where
  "give_index_row y c xs = Inr (y, None) # 
                               give_index_row_rec c xs"

lemma give_index_row_lt_counter:
  assumes "Inr (x0, Some k0) \<in> set (give_index_row y c xs)"
  shows "k0 < incr_row c xs x0"
  using assms proof (induct xs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  then show ?case by (cases "x = x0", auto)
qed


fun synthesize_shuffle_nat :: "'y::enum shuffle \<Rightarrow> 'y \<Rightarrow> ('y + 'y \<times> nat option) list" where
  "synthesize_shuffle_nat s y = give_index_row y (countup_rows_until s y (Enum.enum :: 'y list)) (s y)"

fun enum_convert :: "'k::enum boundedness \<Rightarrow> 'y \<times> nat option \<Rightarrow> ('y \<times> 'k option) list" where
  "enum_convert B (y, None)   = [(y, None)]" |
  "enum_convert B (y, Some k) = [(y, Some (nat_to_enum k))]"

fun synthesize_shuffle :: "'k::enum boundedness \<Rightarrow> 'y::enum shuffle \<Rightarrow> ('y, 'y + 'y \<times> 'k option, 'b) update'" where
  "synthesize_shuffle B s y = map Inl (hat_alpha (enum_convert B) (synthesize_shuffle_nat s y))"


fun synthesize_store :: "'k::enum boundedness \<Rightarrow> ('y::enum, 'k, 'b) store \<Rightarrow> ('y + 'y \<times> 'k option, 'y, 'b) update'" where
  "synthesize_store B store (Inl y)      = [Inl y]" |
  "synthesize_store B store (Inr (y, k)) = map Inr (store (y, k))"

definition synthesize :: "'k::enum boundedness \<Rightarrow> 'y::enum shuffle \<times> ('y, 'k, 'b) store
                      \<Rightarrow> ('y, 'b) update" where
  "synthesize B sa = (case sa of (s, a) \<Rightarrow> synthesize_store B a \<bullet> synthesize_shuffle B s)"


subsection \<open>Properties of Decomposition\<close>


lemma map_alpha_synthesize_shuffle: "t \<star> synthesize_shuffle B s = synthesize_shuffle B s"
  by (rule ext, simp add: map_alpha_apply)

lemma map_alpha_synthesize_store: "t \<star> synthesize_store B p = synthesize_store B (t \<odot> p)"
  by (rule ext_sum, simp add: map_alpha_apply, rule prod.induct, simp add: map_alpha_apply compS_apply)


lemma map_alpha_synthesize: "t \<star> synthesize B (s, a) = synthesize B (s, t \<odot> a)"
  apply (rule ext, simp add: synthesize_def map_alpha_distrib)
  apply (simp add:  map_alpha_synthesize_shuffle map_alpha_synthesize_store)
  done

lemma resolve_idU_idS: "resolve_shuffle idU = idS"
  by (auto simp add: idU_def idS_def resolve_shuffle_def)

(*
lemma resolve_idU_empty:
  fixes B :: "'k::enum boundedness"
  shows "resolve_store B (idU :: ('y::enum, 'b) update) = empty_store"
  unfolding resolve_store_def
proof (rule ext_prod, auto simp add: option.case_eq_if)
  fix y :: "'y"
  show "fst (scan (idU y)) = []" unfolding idU_def by simp
next
  fix y :: "'y" and k :: "'k"
  show "decompose_rec y (enum_to_nat k) (concat_scan_tail idU enum_class.enum) = []"
    apply (rule decompose_rec_alphabet)
     apply (rule concat_scan_tail_idU)
    apply (simp)
    done
qed
*)

lemma resolve_shuffle_distrib_str: 
  "extract_variables (hat_hom \<phi> u) = concat (map (resolve_shuffle \<phi>) (extract_variables u))"
  by (induct u rule: xa_induct, simp_all add: resolve_shuffle_def)

lemma resolve_shuffle_distrib: "resolve_shuffle (\<phi> \<bullet> \<psi>) = resolve_shuffle \<phi> \<odot> resolve_shuffle \<psi>"
  by (rule ext, simp add: compU_apply resolve_shuffle_def resolve_shuffle_distrib_str compS_apply)

lemma resolve_shuffle_map_alpha: "resolve_shuffle (t \<star> m) = resolve_shuffle m"
proof -
  have *: "\<And>u. extract_variables (hat_alpha t u) = extract_variables u"
    by (induct_tac u rule: xa_induct, simp_all)
  show ?thesis by (rule ext, auto simp add: resolve_shuffle_def map_alpha_def *)
qed


subsection \<open>Properties of flat_store and synthesize_store & resolve_store\<close>

subsection \<open>boundedness of Shuffle\<close>

definition bounded_shuffle :: "[nat, 'x shuffle] \<Rightarrow> bool" where
  "bounded_shuffle k f \<equiv> \<forall>x. (\<Sum>y\<in>UNIV. count_list (f y) x) \<le> k"


lemma count_list_extract_variables: "count_list (extract_variables u) x = count_list u (Inl x)"
  by (induct u rule: xa_induct, simp_all)

lemma resolve_bounded:
  fixes m :: "('x::finite, 'b) update"
  assumes "bounded k m"
  shows "bounded_shuffle k (resolve_shuffle m)"
proof (simp add: bounded_shuffle_def resolve_shuffle_def, rule allI)
  fix x
  show "(\<Sum>y\<in>UNIV. count_list (extract_variables (m y)) x) \<le> k"
    using assms unfolding bounded_def count_var_def
    by (simp add: count_list_extract_variables)
qed

lemma resolve_bounded_inverse:
  fixes m :: "('x::finite, 'b) update"
  assumes "bounded_shuffle k (resolve_shuffle m)"
  shows "bounded k m"
  unfolding bounded_def count_var_def proof (auto)
  fix x
  show "(\<Sum>y\<in>UNIV. count_list (m y) (Inl x)) \<le> k"
    using assms unfolding bounded_shuffle_def resolve_shuffle_def
    by (simp add: count_list_extract_variables)
qed

lemma count_extract_variables:
  fixes m :: "('x::finite, 'a) update"
  shows "(\<Sum>y\<in>(UNIV::'x set). count_list u (Inl y)) = length (extract_variables u)"
proof (induct u rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case proof (simp)
    have "(\<Sum>y\<in>(UNIV::'x set). if x = y then count_list xs (Inl y) + 1 else count_list xs (Inl y))
        = (\<Sum>y\<in>(UNIV::'x set). (if x = y then 1 else 0) + count_list xs (Inl y))" (is "?lhs = _")
    proof (rule sum_cong)
      fix x :: "'x"
      show "x \<in> UNIV" by simp
    next
      show "(\<lambda>y. if x = y then count_list xs (Inl y) + 1  else count_list xs (Inl y)) =
            (\<lambda>y. (if x = y then 1 else 0) + count_list xs (Inl y))"
        by auto
    qed
    also have "...  = (\<Sum>y\<in>(UNIV::'x set). (if x = y then 1 else 0)) + (\<Sum>y\<in>(UNIV::'x set). count_list xs (Inl y))"
      by (rule sum.distrib)
    also have "... = Suc (length (extract_variables xs))" (is "_ = ?rhs")
      by (simp add: Var)
    finally show "?lhs = ?rhs".
  qed
next
  case (Alpha a xs)
  then show ?case by simp
qed


lemma variable_count_in_bounded_shuffle:
  fixes s :: "('x::finite) shuffle"
  assumes "bounded_shuffle k s"
  shows "length (s x0) \<le> card (UNIV::'x set) * k"
proof -
  let ?univ = "UNIV::'x set"
  have *: "\<forall>y. (\<Sum>x\<in>?univ. count_list (s x) y) \<le> k" using assms unfolding bounded_shuffle_def by simp
  have "length (s x0) \<le> (\<Sum>x\<in>?univ. length (s x))" by (rule member_le_sum, simp_all)
  also have "... = (\<Sum>x\<in>?univ. (\<Sum>y\<in>?univ. count_list (s x) y))"
    by (rule sum.cong, simp_all add: sum_count_list_UNIV)
  also have "... = (\<Sum>y\<in>?univ. (\<Sum>x\<in>?univ. count_list (s x) y))"
    by (rule sum.commute)
  also have "... \<le> (\<Sum>y\<in>?univ. k)"
    by (rule sum_mono, simp add: *)
  also have "... = card ?univ * k"
    by simp
  finally show ?thesis .
qed

lemma variable_count_in_bounded_update:
  fixes m :: "('x::finite, 'a) update"
  assumes "bounded k m"
  shows "length (extract_variables (m x0)) \<le> card (UNIV::'x set) * k"
  using assms unfolding bounded_def count_var_def
proof -
  have "bounded_shuffle k (resolve_shuffle m)"
    using assms by (simp add: resolve_bounded)
  then have "length (resolve_shuffle m x0) \<le> card (UNIV::'x set) * k"
    by (simp add: variable_count_in_bounded_shuffle)
  then show ?thesis by (simp add: resolve_shuffle_def)
qed

lemma length_scanned_of_variable_count:
  fixes u :: "('x::finite + 'a) list"
  assumes "length (extract_variables u) = k"
  shows "length_scanned (scan u) = k + 1"
using assms proof (induct u arbitrary: k rule: xw_induct)
  case (Word w)
  then show ?case by simp
next
  case (VarWord x w u)
  then show ?case by (simp del: length_scanned.simps)
qed


lemma bounded_copy_length_scanned:
  fixes m :: "('x::finite, 'a) update"
  assumes "bounded k m"
  shows "length_scanned (scan (m x)) \<le> Suc (card (UNIV::'x set) * k)"
proof -
  have "length (extract_variables (m x)) \<le> card (UNIV::'x set) * k"
    using assms by (simp add: variable_count_in_bounded_update)
  then show ?thesis
    by (simp add: length_scanned_of_variable_count)
qed

lemma type_mult_suc_length:
  fixes B :: "'k::enum boundedness"
  assumes "boundedness B k"
  shows "length (Enum.enum::('y::enum, 'k) type_mult_suc list) = Suc (card (UNIV::'y set) * k)"
proof -
  have "card (UNIV::('y, 'k) type_mult_suc set) = card (UNIV::('y \<times> 'k) set) + 1"
    apply (simp add: UNIV_option_conv)
    apply (rule card_image, rule inj_Some)
    done
  also have "... = card (UNIV::'y set) * k + 1"
    using assms unfolding boundedness_def 
    by (auto simp add: card_UNIV_length_enum[symmetric] card_cartesian_product[symmetric])
  finally have "card (UNIV::('y, 'k) type_mult_suc set) = card (UNIV::'y set) * k + 1" .
  then show ?thesis
    by (simp add: card_UNIV_length_enum)
qed

lemma length_scanned_boundedness:
  fixes B :: "'k::enum boundedness"
  fixes m :: "('y::enum, 'b) update"
  assumes "boundedness B k"
  assumes "bounded k m"
  shows "length_scanned (scan (m x)) \<le> length (Enum.enum::('y::enum, 'k) type_mult_suc list)"
  using assms by (simp add: type_mult_suc_length  bounded_copy_length_scanned)
  
(*
theorem resolve_inverse:
  fixes B :: "'k::enum boundedness"
  fixes m :: "('y::enum, 'b) update"
  assumes "bounded k m"
  assumes "boundedness B k"
  shows "synthesize B (resolve_shuffle m, resolve_store B m) = m"
proof -
  have "\<And>x. synthesize B (resolve_shuffle m, resolve_store B m) x = flat (scan (m x))"
    apply (simp add: synthesize_def synthesize_shuffle_def compU_apply)
    apply (simp add: resolve_shuffle_def)
    apply (simp add: padding_scan_ignore_alphabet)
    apply (simp add: concat_map_padding)
    apply (rule flat_store_flat)
    apply (rule length_scanned_boundedness)
    apply (rule assms(2))
    apply (rule assms(1))
    done
  then show ?thesis by (auto simp add: scan_inverse)
qed
  oops
*)

fun store_resolve :: "'k::enum boundedness \<Rightarrow> ('y::enum, 'b) update \<Rightarrow> ('y + 'y \<times> 'k option) \<Rightarrow> ('y + 'b) list" where
  "store_resolve B m (Inl y) = [Inl y]" |
  "store_resolve B m (Inr (y, None))   = map Inr (fst (scan (m y)))" |
  "store_resolve B m (Inr (y, Some k)) = map Inr (lookup (Enum.enum :: 'y list) m y (enum_to_nat k))"

fun store_resolve_nat :: "('y::enum, 'b) update \<Rightarrow> ('y + 'y \<times> nat option) \<Rightarrow> ('y + 'b) list" where
  "store_resolve_nat m (Inl y) = [Inl y]" |
  "store_resolve_nat m (Inr (y, None))   = map Inr (fst (scan (m y)))" |
  "store_resolve_nat m (Inr (y, Some n)) = map Inr (lookup (Enum.enum :: 'y list) m y n)"


lemma store_resolve_eq: "synthesize_store B (resolve_store B m) = store_resolve B m"
proof (rule ext_sum)
  show "\<And>l. synthesize_store B (resolve_store B m) (Inl l) = store_resolve B m (Inl l)"
    unfolding resolve_store_def by simp
next
  fix r
  show "synthesize_store B (resolve_store B m) (Inr r) = store_resolve B m (Inr r)"
  proof (cases "r")
    case (Pair a b)
    then show ?thesis proof (cases "b")
      case None
      then show ?thesis using Pair unfolding resolve_store_def by simp
    next
      case (Some c)
      then show ?thesis using Pair unfolding resolve_store_def by simp
    qed
  qed
qed


fun under_boundedness :: "'k boundedness \<Rightarrow> 'y + 'y \<times> nat option \<Rightarrow> bool" where
  "under_boundedness B (Inl y) = True" |
  "under_boundedness B (Inr (y, None)) = True" |
  "under_boundedness B (Inr (y, Some k)) = (k < card (UNIV::'k set))"

thm give_index_row_lt_counter

lemma
  fixes s :: "'y::enum shuffle"
  assumes "bounded_shuffle K s"
  assumes "boundedness B K"
  shows "list_all (under_boundedness B) (give_index_row y (countup_rows_until s y (Enum.enum :: 'y list)) (s y))"


lemma concat_map_store_resolve_nat:
  fixes B :: "'k::enum boundedness"
  assumes "list_all (under_boundedness B) u"
  shows "concat (map (store_resolve B m) (hat_alpha (enum_convert B) u))
 = concat (map (store_resolve_nat m) u)"
using assms proof (induct u rule: xa_induct)
  case Nil
  then show ?case by simp
next
  case (Var x xs)
  then show ?case by simp
next
  case (Alpha yi xs)
  then show ?case proof (cases yi)
    case (Pair y kn)
    then show ?thesis proof (cases kn)
      case None
      then show ?thesis using Pair Alpha by simp
    next
      case (Some k)
      have "(k < card (UNIV::'k set))" using Alpha Pair Some by simp
      then have "enum_to_nat (nat_to_enum k :: 'k) = k" by (rule nat_enum_iso_UNIV)
      then show ?thesis using Alpha by (simp add: Some Pair)
    qed
  qed
qed




lemma my_great_lemma:
  assumes "Inr (x, Some n) \<in> set (give_index_row y c (extract_variables_pair xas))"
  shows "\<exists>as. lookup_row x n c xas = Some as"
  using assms unfolding resolve_shuffle_def
proof (induct xas arbitrary: c rule: pair_induct)
  case Nil
  then show ?case by simp
next
  case (PairCons x as xas)
  then show ?case by auto
qed

lemma inspect_only_this_row:
  assumes "y \<in> set whole"
  assumes "c = countup_rows_until (resolve_shuffle m) y whole"
  assumes "Inr (x, Some k) \<in> set (give_index_row y c (extract_variables (m y)))"
  shows "lookup_rec m x k whole whole = lookup_row x k c (scan_pair (m y))"
  using assms proof (induct whole rule: rev_induct)
  case Nil
  then show ?case by auto
next
  case (snoc y' whole')
  thm snoc
  show ?case apply (simp add: lookup_rec_last snoc(3))
qed


theorem resolve_inverse:
  fixes B :: "'k::enum boundedness"
  fixes m :: "('y::enum, 'b) update"
  assumes "bounded k m"
  assumes "boundedness B k"
  shows "synthesize B (resolve_shuffle m, resolve_store B m) = m"
  apply (rule ext)
  apply (simp add: synthesize_def)
  apply (simp add: compU_apply store_resolve_eq del: give_index_row.simps add: resolve_shuffle_def)



lemma extract_variables_synthesize_store: "extract_variables (concat (map (synthesize_store B a) u)) = extract_variables u"
  by (induct u rule: xa_induct, simp_all add: synthesize_store_def)

lemma extract_variables_padding_scan: "extract_variables (padding B x (scan (map Inl u))) = u"
proof (induct u rule: rev_induct)
  case Nil
  then show ?case by (simp add: scan_def synthesize_store_def)
next
  case (snoc x xs)
  then show ?case by (simp add: )
qed


theorem synthesize_inverse_shuffle: "resolve_shuffle (synthesize B (s, a)) = s"
  by (auto simp add: synthesize_def resolve_shuffle_def compU_apply
                     extract_variables_synthesize_store extract_variables_padding_scan)

lemma synthesize_prepend_idU: "synthesize_prepend B empty_store = idU"
  by (rule ext, simp add: idU_def)

lemma synthesize_idU: "synthesize B (idS :: 'x \<Rightarrow> 'x list, empty_store) = (idU :: ('x::enum, 'a) update)"
  apply (auto simp add: synthesize_def idU_def idS_def scan_def compU_apply synthesize_prepend_idU)

subsection \<open>Example\<close>

definition poyo :: "(bool, char) update" where
  "poyo = (%z. if z = False then [Inr (CHR ''P''), Inl False, Inr (CHR ''Q''), Inl False, Inr (CHR ''R'')]
        else if z = True then [Inr (CHR ''A''), Inl False, Inr (CHR ''B''), Inl True, Inr (CHR ''C'')]
        else [])"

declare poyo_def [simp]

definition testB :: "bool boundedness" where
  "testB = Type_Nat"


lemma "resolve_store testB poyo (False, None) = ''P''"
  by (simp add: resolve_store_def scan_def enum_to_nat_def enum_option_def enum_prod_def enum_bool_def)
  
lemma "resolve_store testB poyo (False, Some (False, False)) = ''Q''"
  by (simp add: resolve_store_def scan_def enum_to_nat_def enum_option_def enum_prod_def enum_bool_def)

lemma "resolve_store testB poyo (False, Some (False, True)) = ''R''" 
  by (simp add: resolve_store_def scan_def enum_to_nat_def enum_option_def enum_prod_def enum_bool_def)

lemma "resolve_store testB poyo (True, None) = ''A''"
  by (simp add: resolve_store_def scan_def enum_to_nat_def enum_option_def enum_prod_def enum_bool_def)

lemma "resolve_store testB poyo (True, Some (False, False)) = ''B''"
  by (simp add: resolve_store_def scan_def enum_to_nat_def enum_option_def enum_prod_def enum_bool_def)

lemma "resolve_store testB poyo (True, Some (False, True)) = ''C''" 
  by (simp add: resolve_store_def scan_def enum_to_nat_def enum_option_def enum_prod_def enum_bool_def)


end
