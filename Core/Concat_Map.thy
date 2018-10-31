(* Title:   Concat_Map.thy
   Author:  Akama Hitoshi
*)

theory Concat_Map
  imports HOL.List
begin


definition compS :: "('b \<Rightarrow> 'c list) \<Rightarrow> ('a \<Rightarrow> 'b list) \<Rightarrow> 'a \<Rightarrow> 'c list" (infixl "\<odot>" 55) where
  "compS f g = concat o map f o g"

lemma compS_apply: "(f \<odot> g) x = concat (map f (g x))"
  unfolding compS_def by simp

definition idS :: "'a \<Rightarrow> 'a list" where
  "idS x = [x]"

lemma [simp]: "concat (map idS xs) = xs"
  by (induct xs, simp_all add: idS_def)

lemma [simp]: "idS \<odot> f = f"
  by (rule ext, simp add: compS_apply)

lemma [simp]: "f \<odot> idS = f"
  by (rule ext, simp add: compS_apply idS_def)

lemma compS_lem: "concat (map (f \<odot> g) xs) = concat (map f (concat (map g xs)))"
  by (induct xs, simp_all add: compS_apply)

lemma compS_assoc: "(f \<odot> g) \<odot> h = f \<odot> (g \<odot> h)"
  by (rule ext, simp add: compS_apply compS_lem)

hide_fact compS_def



end
