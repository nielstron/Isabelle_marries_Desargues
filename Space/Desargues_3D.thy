theory Desargues_3D
  imports Main Higher_Projective_Space_Rank_Axioms Matroid_Rank_Properties
begin

lemma coplanar_4 :
  assumes "rk {A, B, C} = 3" and "rk {A', B', C'} = 3" and "rk {A, A', P} = 2" and "rk {B, B', P} = 2"
    and "rk {C, C', P} = 2" and "rk {A, B, C, A', B', C'} \<ge> 4" and "rk {B, C, \<alpha>} = 2" 
    and "rk {B', C', \<alpha>} = 2" and "rk {A, C, \<beta>} = 2" and "rk {A', C', \<beta>} = 2" and "rk {A, B, \<gamma>} = 2" 
    and "rk {A', B', \<gamma>} = 2"
  shows "rk {A, B, C, \<alpha>} = 3" and "rk {A', B', C', \<alpha>} = 3"
proof-
  have f1:"rk {A, B, C, \<alpha>} \<ge> 3" using matroid_ax_2
    by (metis assms(1) empty_subsetI insert_mono)
  have "rk {A, B, C, \<alpha>} + rk {B, C} \<le> rk {A, B, C} + rk {B, C, \<alpha>}" using matroid_ax_3_alt
    by (metis Un_insert_right add_One_commute add_mono assms(1) assms(7) matroid_ax_2_alt nat_1_add_1 numeral_plus_one rk_singleton semiring_norm(3) sup_bot.right_neutral)
  then have f2:"rk {A, B, C, \<alpha>} \<le> 3"
    by (metis Un_insert_right add_One_commute assms(7) matroid_ax_2_alt numeral_plus_one semiring_norm(3) sup_bot.right_neutral)
  from f1 and f2 show "rk {A, B, C, \<alpha>} = 3" by auto
(* Note that the points A, B, C and A', B', C' have symmetric roles, so the same result holds for 
the points A', B' and C' *)
  thus "rk {A', B', C', \<alpha>} = 3"
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right antisym_conv assms(2) assms(8) insert_is_Un matroid_ax_2_alt nat_1_add_1 numeral_2_eq_2 numeral_3_eq_3)
qed

lemma coplanar_4_bis :
  assumes "rk {A, B, C} = 3" and "rk {A', B', C'} = 3" and "rk {A, A', P} = 2" and "rk {B, B', P} = 2"
    and "rk {C, C', P} = 2" and "rk {A, B, C, A', B', C'} \<ge> 4" and "rk {B, C, \<alpha>} = 2" 
    and "rk {B', C', \<alpha>} = 2" and "rk {A, C, \<beta>} = 2" and "rk {A', C', \<beta>} = 2" and "rk {A, B, \<gamma>} = 2" 
    and "rk {A', B', \<gamma>} = 2"
  shows "rk {A, B, C, \<beta>} = 3" and "rk {A', B', C', \<beta>} = 3"
proof-
  have f1:"rk {A, B, C, \<beta>} \<ge> 3" using matroid_ax_2
    by (metis assms(1) empty_subsetI insert_mono)
  have "rk {A, B, C, \<beta>} + rk {A, C} \<le> rk {A, B, C} + rk {A, C, \<beta>}" using matroid_ax_3_alt
    by (smt One_nat_def add_Suc_right add_leD1 add_le_mono assms(1) assms(9) insert_commute insert_is_Un matroid_ax_3 numeral_2_eq_2 numeral_3_eq_3 one_add_one rk_singleton)
  then have f2:"rk {A, B, C, \<beta>} \<le> 3"
    by (smt One_nat_def Suc_le_mono add_le_cancel_right assms(1) assms(9) f1 insert_absorb2 insert_commute nat.inject numeral_2_eq_2 numeral_3_eq_3 rk_couple rk_singleton_bis)
  from f1 and f2 show "rk {A, B, C, \<beta>} = 3" by auto
  thus "rk {A', B', C', \<beta>} = 3"
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right arith_special(3) assms(10) assms(2) insert_is_Un le_antisym matroid_ax_2_alt numeral_2_eq_2 numeral_3_eq_3)
qed

lemma coplanar_4_ter :
  assumes "rk {A, B, C} = 3" and "rk {A', B', C'} = 3" and "rk {A, A', P} = 2" and "rk {B, B', P} = 2"
    and "rk {C, C', P} = 2" and "rk {A, B, C, A', B', C'} \<ge> 4" and "rk {B, C, \<alpha>} = 2" 
    and "rk {B', C', \<alpha>} = 2" and "rk {A, C, \<beta>} = 2" and "rk {A', C', \<beta>} = 2" and "rk {A, B, \<gamma>} = 2" 
    and "rk {A', B', \<gamma>} = 2"
  shows "rk {A, B, C, \<gamma>} = 3" and "rk {A', B', C', \<gamma>} = 3"
proof-
  have f1:"rk {A, B, C, \<gamma>} \<ge> 3" using matroid_ax_2
    by (metis assms(1) empty_subsetI insert_mono)
  have "rk {A, B, C, \<gamma>} + rk {A, B} \<le> rk {A, B, C} + rk {A, B, \<gamma>}" 
    using matroid_ax_3_alt[of "{A, B}" "{A, B, C}" "{A, B, \<gamma>}"]
    by (simp add: insert_commute)
  then have f2:"rk {A, B, C, \<gamma>} \<le> 3"
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right assms(11) insert_is_Un matroid_ax_2_alt numeral_2_eq_2 numeral_3_eq_3 one_add_one)
  from f1 and f2 show "rk {A, B, C, \<gamma>} = 3" by auto
  thus "rk {A', B', C', \<gamma>} = 3"
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right assms(12) assms(2) insert_is_Un le_antisym matroid_ax_2_alt nat_1_add_1 numeral_2_eq_2 numeral_3_eq_3)
qed

lemma coplanar_5 :
  assumes "rk {A, B, C} = 3" and "rk {A', B', C'} = 3" and "rk {A, A', P} = 2" and "rk {B, B', P} = 2"
    and "rk {C, C', P} = 2" and "rk {A, B, C, A', B', C'} \<ge> 4" and "rk {B, C, \<alpha>} = 2" 
    and "rk {B', C', \<alpha>} = 2" and "rk {A, C, \<beta>} = 2" and "rk {A', C', \<beta>} = 2" and "rk {A, B, \<gamma>} = 2" 
    and "rk {A', B', \<gamma>} = 2"
  shows "rk {A, B, C, \<alpha>, \<beta>} = 3" and "rk {A', B', C', \<alpha>, \<beta>} = 3"
proof-
  have f1:"rk {A, B, C, \<alpha>} = 3" using coplanar_4
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right assms(1) assms(7) insert_is_Un le_antisym matroid_ax_2_alt numeral_2_eq_2 numeral_3_eq_3 one_add_one)
  have f2:"rk {A, B, C, \<beta>} = 3" using coplanar_4_bis
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right assms(1) assms(9) insert_is_Un le_antisym matroid_ax_2_alt numeral_2_eq_2 numeral_3_eq_3 one_add_one)
  from f1 and f2 show "rk {A, B, C, \<alpha>, \<beta>} = 3" 
    using matroid_ax_3_alt'
    by (metis Un_assoc assms(1) insert_is_Un)
  have f1':"rk {A', B', C', \<alpha>} = 3" using coplanar_4
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right arith_special(3) assms(2) assms(8) insert_is_Un le_antisym matroid_ax_2_alt numeral_2_eq_2 numeral_3_eq_3)
  have f2':"rk {A', B', C', \<beta>} = 3" using coplanar_4_bis
    by (smt One_nat_def Un_commute add.commute add_Suc_right assms(10) assms(2) insert_commute insert_is_Un le_antisym matroid_ax_2_alt nat_1_add_1 numeral_2_eq_2 numeral_3_eq_3)
  from f1' and f2' show "rk {A', B', C', \<alpha>, \<beta>} = 3"
    using matroid_ax_3_alt'
    by (metis Un_assoc assms(2) insert_is_Un)
qed

lemma coplanar_5_bis :
  assumes "rk {A, B, C} = 3" and "rk {A', B', C'} = 3" and "rk {A, A', P} = 2" and "rk {B, B', P} = 2"
    and "rk {C, C', P} = 2" and "rk {A, B, C, A', B', C'} \<ge> 4" and "rk {B, C, \<alpha>} = 2" 
    and "rk {B', C', \<alpha>} = 2" and "rk {A, C, \<beta>} = 2" and "rk {A', C', \<beta>} = 2" and "rk {A, B, \<gamma>} = 2" 
    and "rk {A', B', \<gamma>} = 2"
  shows "rk {A, B, C, \<alpha>, \<gamma>} = 3" and "rk {A', B', C', \<alpha>, \<gamma>} = 3"
proof-
  have f1:"rk {A, B, C, \<alpha>} = 3" using coplanar_4
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right assms(1) assms(7) insert_is_Un le_antisym matroid_ax_2_alt numeral_2_eq_2 numeral_3_eq_3 one_add_one)
  have f2:"rk {A, B, C, \<gamma>} = 3" using coplanar_4_ter
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right assms(1) assms(11) insert_is_Un le_antisym matroid_ax_2_alt numeral_2_eq_2 numeral_3_eq_3 one_add_one)
  from f1 and f2 show "rk {A, B, C, \<alpha>, \<gamma>} = 3" 
    using matroid_ax_3_alt'
    by (metis Un_assoc assms(1) insert_is_Un)
  have f1':"rk {A', B', C', \<alpha>} = 3" using coplanar_4
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right arith_special(3) assms(2) assms(8) insert_is_Un le_antisym matroid_ax_2_alt numeral_2_eq_2 numeral_3_eq_3)
  have f2':"rk {A', B', C', \<gamma>} = 3" using coplanar_4_ter
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right arith_special(3) assms(12) assms(2) insert_is_Un le_antisym matroid_ax_2_alt numeral_2_eq_2 numeral_3_eq_3)
  from f1' and f2' show "rk {A', B', C', \<alpha>, \<gamma>} = 3"
    using matroid_ax_3_alt'
    by (metis Un_assoc assms(2) insert_is_Un)
qed

lemma coplanar_6 :
  assumes "rk {A, B, C} = 3" and "rk {A', B', C'} = 3" and "rk {A, A', P} = 2" and "rk {B, B', P} = 2"
    and "rk {C, C', P} = 2" and "rk {A, B, C, A', B', C'} \<ge> 4" and "rk {B, C, \<alpha>} = 2" 
    and "rk {B', C', \<alpha>} = 2" and "rk {A, C, \<beta>} = 2" and "rk {A', C', \<beta>} = 2" and "rk {A, B, \<gamma>} = 2" 
    and "rk {A', B', \<gamma>} = 2"
  shows "rk {A, B, C, \<alpha>, \<beta>, \<gamma>} = 3" and "rk {A', B', C', \<alpha>, \<beta>, \<gamma>} = 3"
proof-
  have f1:"rk {A, B, C, \<alpha>, \<gamma>} = 3" 
    using coplanar_5_bis[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] assms(1) assms(10) assms(11) assms(12) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) 
    by blast
  have f2:"rk {A, B, C, \<alpha>, \<beta>} = 3"
    using coplanar_5[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] assms(1) assms(10) assms(11) assms(12) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) 
    by blast
  have f3:"rk {A, B, C, \<alpha>} = 3" 
    using coplanar_4
    by (smt One_nat_def Un_assoc Un_commute add.commute add_Suc_right assms(1) assms(7) insert_is_Un le_antisym matroid_ax_2_alt numeral_2_eq_2 numeral_3_eq_3 one_add_one)
  from f1 and f2 and f3 show "rk {A, B, C, \<alpha>, \<beta>, \<gamma>} = 3" 
    using matroid_ax_3_alt'[of "{A, B, C, \<alpha>}" "\<beta>" "\<gamma>"]
    by (metis Un_insert_left sup_bot.left_neutral)
  have f1':"rk {A', B', C', \<alpha>, \<gamma>} = 3" 
    using coplanar_5_bis[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] assms(1) assms(10) assms(11) assms(12) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) 
    by blast
  have f2':"rk {A', B', C', \<alpha>, \<beta>} = 3"
    using coplanar_5[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] assms(1) assms(10) assms(11) assms(12) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) 
    by blast
  have f3':"rk {A', B', C', \<alpha>} = 3"
    using coplanar_4
    by (smt Un_commute Un_insert_left add_One_commute assms(2) assms(8) insert_is_Un le_antisym matroid_ax_2_alt numeral_plus_one semiring_norm(3))
  from f1' f2' f3' show "rk {A', B', C', \<alpha>, \<beta>, \<gamma>} = 3"
    using matroid_ax_3_alt'[of "{A', B', C', \<alpha>}" "\<beta>" "\<gamma>"]
    by (metis Un_insert_left sup_bot.left_neutral)
qed

lemma non_coplanar :
  assumes "rk {A, B, C} = 3" and "rk {A', B', C'} = 3" and "rk {A, A', P} = 2" and "rk {B, B', P} = 2"
    and "rk {C, C', P} = 2" and "rk {A, B, C, A', B', C'} \<ge> 4" and "rk {B, C, \<alpha>} = 2" 
    and "rk {B', C', \<alpha>} = 2" and "rk {A, C, \<beta>} = 2" and "rk {A', C', \<beta>} = 2" and "rk {A, B, \<gamma>} = 2" 
    and "rk {A', B', \<gamma>} = 2"
  shows "rk {A, B, C, A', B', C', \<alpha>, \<beta>, \<gamma>} \<ge> 4" 
proof-
  have "rk {A, B, C, A', B', C'} \<le> rk {A, B, C, A', B', C', \<alpha>, \<beta>, \<gamma>}" using matroid_ax_2 by auto
  thus "4 \<le> rk {A, B, C, A', B', C', \<alpha>, \<beta>, \<gamma>}" using matroid_ax_2 assms(6) by linarith
qed

theorem desargues_3D :
  assumes "rk {A, B, C} = 3" and "rk {A', B', C'} = 3" and "rk {A, A', P} = 2" and "rk {B, B', P} = 2"
    and "rk {C, C', P} = 2" and "rk {A, B, C, A', B', C'} \<ge> 4" and "rk {B, C, \<alpha>} = 2" 
    and "rk {B', C', \<alpha>} = 2" and "rk {A, C, \<beta>} = 2" and "rk {A', C', \<beta>} = 2" and "rk {A, B, \<gamma>} = 2" 
    and "rk {A', B', \<gamma>} = 2"
  shows "rk {\<alpha>, \<beta>, \<gamma>} \<le> 2"
proof-
  have "rk {A, B, C, A', B', C', \<alpha>, \<beta>, \<gamma>} + rk {\<alpha>, \<beta>, \<gamma>} \<le> rk {A, B, C, \<alpha>, \<beta>, \<gamma>} + rk {A', B', C', \<alpha>, \<beta>, \<gamma>}"
    using matroid_ax_3_alt[of "{\<alpha>, \<beta>, \<gamma>}" "{A, B, C, \<alpha>, \<beta>, \<gamma>}" "{A', B', C', \<alpha>, \<beta>, \<gamma>}"]
    by (simp add: insert_commute)
  then have "rk {\<alpha>, \<beta>, \<gamma>} \<le> rk {A, B, C, \<alpha>, \<beta>, \<gamma>} + rk {A', B', C', \<alpha>, \<beta>, \<gamma>} - rk {A, B, C, A', B', C', \<alpha>, \<beta>, \<gamma>}"
    by linarith
  thus "rk {\<alpha>, \<beta>, \<gamma>} \<le> 2" using coplanar_6[of A B C A' B' C' P \<alpha> \<beta> \<gamma>] non_coplanar[of A B C A' B' C' P \<alpha> \<beta> \<gamma>]
    by (smt Nat.le_add_diff \<open>rk {A, B, C, A', B', C', \<alpha>, \<beta>, \<gamma>} + rk {\<alpha>, \<beta>, \<gamma>} \<le> rk {A, B, C, \<alpha>, \<beta>, \<gamma>} + rk {A', B', C', \<alpha>, \<beta>, \<gamma>}\<close> add_diff_cancel_right' add_leD1 assms(1) assms(10) assms(11) assms(12) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) assms(8) assms(9) diff_diff_left le_add_diff_inverse numeral_plus_one semiring_norm(2) semiring_norm(5) semiring_norm(8))
qed








