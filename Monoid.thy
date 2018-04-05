theory Monoid
  imports Main
begin

class monoid =
  fixes unit :: 'a ("\<one>")
    and mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<bullet>" 70)
  assumes assoc: "(x \<bullet> y) \<bullet> z = x \<bullet> (y \<bullet> z)"
      and lunit: "\<one> \<bullet> x = x"
      and runit: "x \<bullet> \<one> = x"

instantiation list :: (type) monoid
begin

definition
  unit_list_def: "unit = []"

definition
  mult_list_def: "mult as bs = as @ bs"

instance proof
  fix i j k :: "'a list"
  show "mult (mult i j) k = mult i (mult j k)" by (simp add: mult_list_def)
next
  fix x :: "'a list"
  show "unit \<bullet> x = x" by (simp add: mult_list_def unit_list_def)
next
  fix x :: "'a list"
  show "x \<bullet> \<one> = x" by (simp add: mult_list_def unit_list_def)
qed

definition
  "twice x = mult x x"

lemma "mult x (twice x) = mult (twice x) x"
  by (simp add: twice_def assoc)

end
