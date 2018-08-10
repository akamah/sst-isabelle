theory Shuffle
  imports Main Enum List "../Util/Enum_Nat" "../Core/Update" "../Single_Use/Single_Use" "Decompose_Update"
begin                                  


typedef (overloaded) ('e::enum, 'x::finite) bc_shuffle =
  "{\<alpha> :: 'x shuffle. bounded_shuffle (length (Enum.enum :: 'e list)) \<alpha>}"
  morphisms Rep_bc_shuffle Abs_bc_shuffle
proof
  show "emptyS \<in> {\<alpha> :: 'x shuffle. bounded_shuffle (length (Enum.enum :: 'e list)) \<alpha>}"
    unfolding emptyS_def bounded_shuffle_def by simp
qed


lemma list_length_set_Suc:
  "{xs. length xs = Suc k} = (\<Union>x::'a\<in>UNIV. \<Union>xs\<in>{xs. length xs = k}. { x # xs })" (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs" proof (auto, intro exI, auto)
    fix xs :: "'a list"
    show "length xs = Suc k \<Longrightarrow> length (tl xs) = k" by simp
  next
    fix xs :: "'a list"
    show "length xs = Suc k \<Longrightarrow> xs = hd xs # tl xs" by (cases "xs", simp_all)
  qed
next
  show "?rhs \<subseteq> ?lhs" by (auto)
qed

lemma list_length_le_Suc:
  "{xs::'a list. length xs < Suc k} = {xs::'a list. length xs = k} \<union> {xs::'a list. length xs < k}" (is "?lhs = ?rhs")
  by (auto)

lemma finite_list_length_set:
  "finite {xs. length xs = k}"
proof (induct k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case apply (simp add: list_length_set_Suc)
    find_theorems "finite (\<Union>x\<in>?A. ?f x)"
qed

lemma "finite {l :: 'a::finite list. length l < k}"
proof (induct k)
  case 0
  then show ?case by simp
next
  case (Suc k)
  then show ?case proof -
    assume "finite {l::'a list. length l < k}"
    have "{xs::'a list. length xs < Suc k} = {xs::'a list. length xs = k} \<union> {xs::'a list. length xs < k}"
      by (simp add: list_length_le_Suc)

qed



instance bc_shuffle :: (enum, finite) finite
proof
  show "finite (UNIV :: ('e::enum, 'x::finite) bc_shuffle set)"
  proof (rule finite_imageD)
    let ?graph = "\<lambda>f::'x \<Rightarrow> 'x list. {(




end
