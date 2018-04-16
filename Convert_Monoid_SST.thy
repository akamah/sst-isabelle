(* Title:   Convert_Monoid_SST.thy
   Author:  Akama Hitoshi
*)

section \<open>Convert a Monoid SST to a ordinary SST\<close>

theory Convert_Monoid_SST
  imports Main Update SST Monoid_SST Decompose_update
begin

subsection \<open>Definition of another strange Transducer\<close>


definition \<iota> :: "('x \<Rightarrow> 'y shuffle) \<Rightarrow> 'x \<Rightarrow> ('y, 'x \<times> 'y location) update" where
  "\<iota> \<alpha> x = synthesize (\<alpha> x, (\<lambda>y'. [(x, Inl y')]), (\<lambda>y. [(x, Inr y)]))"

definition \<iota>1 :: "('x \<Rightarrow> 'y shuffle) \<Rightarrow> 'x \<Rightarrow> (('y, 'x \<times> 'y location) update + 'b) list" where
  "\<iota>1 \<alpha> x = [Inl (\<iota> \<alpha> x)]"

(* TODO: define \<tau> 

definition \<tau> :: "(('y, 'x \<times> 'y location) update + ('y, 'b) update) list \<Rightarrow> ('y, 'x \<times> 'y location + 'b) update" where
  

definition \<box> :: "('x \<Rightarrow> 'x shuffle) \<times> ('x, ('y, 'b) update) update \<Rightarrow> ('x \<Rightarrow> 'x shuffle)" where
  "\<box> \<alpha> \<theta> = "

*)

end
