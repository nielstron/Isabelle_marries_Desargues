theory Desargues_Property
  imports Main Projective_Plane_Axioms Pappus_Property Pascal_Property
begin

(* Contents:
- We give Desargues's property, [desargues_prop], that states that if two triangles are perspective 
from a point, then they are perspective from a line. 
Note that some planes satisfy that property and some others don't, hence Desargues's property is
not a theorem though it is a theorem in projective space geometry *)

definition distinct3 :: "[Points, Points, Points] \<Rightarrow> bool" where
"distinct3 A B C \<equiv> A \<noteq> B \<and> A \<noteq> C \<and> B \<noteq> C"

definition triangle :: "[Points, Points, Points] \<Rightarrow> bool" where
"triangle A B C \<equiv> distinct3 A B C \<and> (line A B \<noteq> line A C)"

definition meet_in :: "Lines \<Rightarrow> Lines => Points => bool " where
"meet_in l m P \<equiv> incid P l \<and> incid P m"

lemma meet_col_1:
  assumes "meet_in (line A B) (line C D) P"
  shows "col A B P"
  using assms col_def incidA_lAB incidB_lAB meet_in_def by blast

lemma meet_col_2:
  assumes "meet_in (line A B) (line C D) P"
  shows "col C D P"
  using assms meet_col_1 meet_in_def by auto

definition meet_3_in :: "[Lines, Lines, Lines, Points] \<Rightarrow> bool" where
"meet_3_in l m n P \<equiv> meet_in l m P \<and> meet_in l n P"

lemma meet_all_3:
  assumes "meet_3_in l m n P"
  shows "meet_in m n P"
  using assms meet_3_in_def meet_in_def by auto

lemma meet_comm:
  assumes "meet_in l m P"
  shows "meet_in m l P"
  using assms meet_in_def by auto

lemma meet_3_col_1:
  assumes "meet_3_in (line A B) m n P"
  shows "col A B P"
  using assms meet_3_in_def meet_col_2 meet_in_def by auto

lemma meet_3_col_2:
  assumes "meet_3_in l (line A B) n P"
  shows "col A B P"
  using assms col_def incidA_lAB incidB_lAB meet_3_in_def meet_in_def by blast

lemma meet_3_col_3:
  assumes "meet_3_in l m (line A B) P"
  shows "col A B P"
  using assms meet_3_col_2 meet_3_in_def by auto

definition distinct7 ::
  "[Points, Points, Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"distinct7 A B C D E F G \<equiv> (A \<noteq> B) \<and> (A \<noteq> C) \<and> (A \<noteq> D) \<and> (A \<noteq> E) \<and> (A \<noteq> F) \<and> (A \<noteq> G) \<and>
(B \<noteq> C) \<and> (B \<noteq> D) \<and> (B \<noteq> E) \<and> (B \<noteq> F) \<and> (B \<noteq> G) \<and>
(C \<noteq> D) \<and> (C \<noteq> E) \<and> (C \<noteq> F) \<and> (C \<noteq> G) \<and>
(D \<noteq> E) \<and> (D \<noteq> F) \<and> (D \<noteq> G) \<and>
(E \<noteq> F) \<and> (E \<noteq> G) \<and>
(F \<noteq> G)"

definition distinct3l :: "[Lines, Lines, Lines] \<Rightarrow> bool" where
"distinct3l l m n \<equiv> l \<noteq> m \<and> l \<noteq> n \<and> m \<noteq> n"

(* From now on we give less general statements on purpose to avoid a lot of uninteresting 
degenerate cases, since we can hardly think of any interesting application where one would need 
to instantiate a statement on such degenerate case, hence our statements and proofs will be more 
textbook-like. For the working mathematician the only thing that probably matters is the main
theorem without considering all the degenerate cases for which the statement might still hold. *)

definition are_perspective_from_point :: 
  "[Points, Points, Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"are_perspective_from_point A B C A' B' C' P \<equiv> distinct7 A B C A' B' C' P \<and> triangle A B C \<and>
triangle A' B' C' \<and> distinct3l (line A A') (line B B') (line C C') \<and> 
meet_3_in (line A A') (line B B') (line C C') P"

definition are_perspective_from_line ::
  "[Points, Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"are_perspective_from_line A B C A' B' C' \<equiv> distinct6 A B C A' B' C' \<and> triangle A B C \<and>
triangle A' B' C' \<and> line A B \<noteq> line A' B' \<and> line A C \<noteq> line A' C' \<and> line B C \<noteq> line B' C' \<and>
col (inter (line A B) (line A' B')) (inter (line A C) (line A' C')) (inter (line B C) (line B' C'))"

definition desargues_prop :: "bool" where
"desargues_prop \<equiv> 
\<forall>A B C A' B' C' P. are_perspective_from_point A B C A' B' C' P \<longrightarrow> are_perspective_from_line A B C A' B' C'"

end






