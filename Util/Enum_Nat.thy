(* Title:   Enum_Nat.thy
   Author:  Akama Hitoshi
*)

theory Enum_Nat
  imports HOL.Enum
begin


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
  shows "nat_to_enum (enum_to_nat e) = e"
  unfolding nat_to_enum_def enum_to_nat_def
  by (rule list_nat_iso, simp add: enum_UNIV)

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

lemma nat_enum_iso_UNIV:
  assumes "n < card (UNIV :: ('e::enum) set)"
  shows "enum_to_nat (nat_to_enum n :: 'e) = n"
  by (rule nat_enum_iso, simp add: card_UNIV_length_enum[symmetric] assms)

lemma enum_ex_zero:
  assumes "0 < length (Enum.enum :: ('e::enum) list)"
  shows "\<exists>k0::'e. (enum_to_nat k0 = 0)"
proof
  let ?k0 = "nat_to_enum 0 :: 'e"
  show "enum_to_nat ?k0 = 0"
    using assms by (simp add: nat_enum_iso)
qed

lemma list_nat_less:
  assumes "e \<in> set xs"
  shows "enum_to_nat' xs e < length xs"
using assms proof (induct xs)
  case Nil
  then show ?case by simp
next
  case (Cons a xs)
  then show ?case by (cases "e = a", simp_all)
qed

lemma enum_nat_less:
  fixes k :: "'e::enum"
  shows "enum_to_nat k < length (Enum.enum :: 'e list)"
  unfolding enum_to_nat_def
  by (rule list_nat_less, simp add: enum_UNIV)


lemma inj_list_to_nat:
  assumes "distinct xs"
  shows "inj_on (enum_to_nat' xs) (set xs)"
using assms unfolding inj_on_def by (induct xs, simp_all)

lemma inj_enum_to_nat:
  "inj enum_to_nat"
  unfolding enum_to_nat_def
  by (simp add: UNIV_enum inj_list_to_nat[OF enum_distinct])

lemma inj_nat_to_enum':
  assumes "distinct xs"
  shows "inj_on (nat_to_enum' xs) {i. i < length xs}"
proof -
  show ?thesis unfolding inj_on_def using assms
  proof (induct xs)
    case Nil
    then show ?case by simp
  next
    case (Cons a xs)
    then show ?case by (auto, case_tac x; case_tac y, auto simp add: nat_to_enum'_in)
  qed
qed  

lemma inj_nat_to_enum:
  "inj_on (nat_to_enum :: nat \<Rightarrow> 'k::enum) {i. i < length (Enum.enum :: 'k list)}"
  unfolding nat_to_enum_def
  using enum_distinct 
  by (rule inj_nat_to_enum')

text \<open>Type-level natural number\<close>
datatype ('i::enum) type_nat = Type_Nat

definition type_mult :: "'i::enum type_nat \<Rightarrow> 'j::enum type_nat \<Rightarrow> ('i \<times> 'j) type_nat" where
  "type_mult A B = Type_Nat"

definition type_suc :: "'i::enum type_nat \<Rightarrow> ('i option) type_nat" where
  "type_suc A = Type_Nat"


section \<open>Utility\<close>

lemma length_enum_gt_0: "0 < length (Enum.enum :: 'e::enum list)"
proof -
  have "0 < card (UNIV :: 'e set)"
    by (simp add: finite_UNIV_card_ge_0)
  then show ?thesis    
    by (simp add: card_UNIV_length_enum)
qed

lemma enum_ne_Nil: "(Enum.enum :: 'e::enum list) \<noteq> []"
  using length_enum_gt_0 by simp

lemma nat_enum_zero:
  shows "enum_to_nat (nat_to_enum 0 :: 'e::enum) = 0"
  by (rule nat_enum_iso, rule length_enum_gt_0)

lemma enum_nat_zero_then_nat_enum_zero:
  "enum_to_nat (z :: 'e::enum) = 0 \<Longrightarrow> nat_to_enum 0 = z"
proof -
  assume *: "enum_to_nat z = 0"
  show "nat_to_enum 0 = z"
    by (simp add: *[symmetric] enum_nat_iso enum_UNIV)
qed

end
