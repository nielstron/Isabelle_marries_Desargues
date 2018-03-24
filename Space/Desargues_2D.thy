theory Desargues_2D
  imports Main Higher_Projective_Space_Rank_Axioms Matroid_Rank_Properties
begin

(*
Contents:
- We prove Desargues's theorem: if two triangles ABC and A'B'C' are perspective from a point P (ie. 
the lines AA', BB' and CC' are concurrent in P), then they are perspective from a line (ie. the points
\<alpha> = BC \<inter> B'C', \<beta> = AC \<inter> A'C' and \<gamma> = AB \<inter> A'B' are collinear).
In this file we restrict ourself to the case where the two triangles ABC and A'B'C' are coplanar. 
*)

definition desargues_config_2D :: "[Points, Points, Points, Points, Points, Points, Points, Points, Points, Points] \<Rightarrow> bool" 
  where "desargues_config_2D A B C A' B' C' P \<alpha> \<beta> \<gamma> \<equiv> rk {A, B, C} = 3 \<and> rk {A', B', C'} = 3 \<and> 
rk {A, A', P} = 2 \<and> rk {B, B', P} = 2 \<and> rk {C, C', P} = 2 \<and> rk {A, B, \<gamma>} = 2 \<and> rk {A', B', \<gamma>} = 2 \<and>
rk {A, C, \<beta>} = 2 \<and> rk {A', C', \<beta>} = 2 \<and> rk {B, C, \<alpha>} = 2 \<and> rk {B', C', \<alpha>} = 2 \<and> 
rk {A, B, C, A', B', C'} = 3 \<and> 
(* We add the following non-degeneracy conditions *)
rk {A, B, P} = 3 \<and> rk {A, C, P} = 3 \<and> rk {B, C, P} = 3 \<and> 
rk {A, A'} = 2 \<and> rk {B, B'} = 2 \<and> rk {C, C'} = 2"

lemma coplanar_ABCA'B'C'P :
  assumes "desargues_config_2D A B C A' B' C' P \<alpha> \<beta> \<gamma>"
  shows "rk {A, B, C, A', B', C', P} = 3"
proof-
  have "rk {A, B, C, A', B', C', P} + rk {A, A'} \<le> rk {A, B, C, A', B', C'} + rk {A, A', P}"
    using matroid_ax_3_alt[of "{A, A'}" "{A, B, C, A', B', C'}" "{A, A', P}"]
    by (simp add: insert_commute)
  then have "rk {A, B, C, A', B', C', P} \<le> 3" 
    using assms desargues_config_2D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>]
    by linarith
  then show "rk {A, B, C, A', B', C', P} = 3" 
    using assms desargues_config_2D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] matroid_ax_2
    by (metis Un_insert_right Un_upper2 le_antisym sup_bot.right_neutral)
qed

lemma non_colinear_A'B'P :
  assumes "rk {A, B, P} = 3" and "rk {A, A', P} = 2" and "rk {B, B', P} = 2" and "rk {A', P} = 2" 
and "rk {B', P} = 2"
  shows "rk {A', B', P} = 3" 
proof-
  have f1:"rk {A', B', P} \<le> 3" 
    using rk_triple_le by auto
  have "rk {A, B, A', B', P} \<ge> 3" 
    using assms(1) matroid_ax_2
    by (metis insert_mono insert_subset subset_insertI)
  then have f2:"rk {A, B, A', B', P} = 3" 
    using matroid_ax_3_alt[of "{P}" "{A, A', P}" "{B, B', P}"] assms(2) assms(3)
    by (simp add: insert_commute rk_singleton)
  have "rk {A, B, A', B', P} + rk {B', P} \<le> rk {A, A', B', P} + rk {B, B', P}" 
    using matroid_ax_3_alt[of "{B', P}" "{A, A', B', P}" "{B, B', P}"]
    by (simp add: insert_commute)
  then have "rk {A, A', B', P} \<ge> 3" 
    using f2 assms(3) assms(5) by linarith
  then have f3:"rk {A, A', B', P} = 3" 
    using f2 matroid_ax_2
    by (metis eq_iff insert_commute subset_insertI)
  have "rk {A, A', B', P} + rk {A', P} \<le> rk {A', B', P} + rk {A, A', P}" 
    using matroid_ax_3_alt[of "{A', P}" "{A', B', P}" "{A, A', P}"]
    by (simp add: insert_commute)
  then have "rk {A', B', P} \<ge> 3" 
    using f3 assms(2) assms(4) by linarith
  thus "rk {A', B', P} = 3" 
    using f1 by auto
qed

lemma desargues_config_2D_non_colinear :
  assumes "desargues_config_2D A B C A' B' C' P \<alpha> \<beta> \<gamma>" and "rk {A', P} = 2" and "rk {B', P} = 2" 
and "rk {C', P} = 2"
  shows "rk {A', B', P} = 3" and "rk {A', C', P} = 3" and "rk {B', C', P} = 3"
proof-
  show "rk {A', B', P} = 3" 
    using non_colinear_A'B'P assms(1) desargues_config_2D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] assms(2) assms(3)
    by blast
  show "rk {A', C', P} = 3"
    using non_colinear_A'B'P assms(1) desargues_config_2D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] assms(2) assms(4)
    by blast
  show "rk {B', C', P} = 3"
    using non_colinear_A'B'P assms(1) desargues_config_2D_def[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] assms(3) assms(4)
    by blast
qed

theorem desargues_2D :
  assumes "desargues_config_2D A B C A' B' C' P \<alpha> \<beta> \<gamma>"
  shows "rk {\<alpha>, \<beta>, \<gamma>} \<le> 2"