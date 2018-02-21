theory Matroid_Rank_Properties
  imports Main Higher_Projective_Space_Rank_Axioms
begin

lemma matroid_ax_3_alt:
  assumes "I \<subseteq> X \<inter> Y"
  shows "rk (X \<union> Y) + rk I \<le> rk X + rk Y"
  by (metis add.commute add_le_cancel_right assms matroid_ax_2 matroid_ax_3 order_trans)

lemma rk_uniqueness:
  assumes "rk {A,B} = 2" and "rk {C,D} = 2" and "rk {A,B,M} \<le> 2" and "rk {C,D,M} \<le> 2" and
  "rk {A,B,P} \<le> 2" and "rk {C,D,P} \<le> 2" and "rk {A,B,C,D} \<ge> 3"
  shows "rk {M,P} = 1"
proof-
  have "{A,B,M} \<union> {A,B,P} = {A,B,M,P}"
    by auto
  have "rk {A,B,M,P} + rk {A,B} \<le> rk {A,B,M} + rk {A,B,P}"
    by (metis (full_types) \<open>{A, B, M} \<union> {A, B, P} = {A, B, M, P}\<close> insert_commute le_inf_iff matroid_ax_3_alt subset_insertI)
  then have "rk {A,B,M,P} = 2"
    by (smt Un_upper1 Un_upper2 \<open>{A, B, M} \<union> {A, B, P} = {A, B, M, P}\<close> add_diff_cancel_left' add_diff_cancel_right' add_mono antisym assms(1) assms(3) assms(5) le_diff_conv matroid_ax_2)
  have "{C,D,M} \<union> {C,D,P} = {C,D,M,P}"
    by auto
  have "rk {C,D,M,P} + rk {C,D} \<le> rk {C,D,M} + rk {C,D,P}"
    by (metis Un_insert_left Un_upper1 \<open>{C, D, M} \<union> {C, D, P} = {C, D, M, P}\<close> insert_is_Un le_inf_iff matroid_ax_3_alt)
  then have i1:"rk {C,D,M,P} + 2 \<le> 4"
    using assms(2) assms(4) assms(6) by linarith
  moreover have i2:"rk {C,D,M,P} \<ge> 2"
    by (metis assms(2) insertI1 insert_subset matroid_ax_2 subset_insertI)
  from i1 and i2 have "rk {C,D,M,P} = 2"
    by linarith
  have "rk {A,B,C,D,M,P} \<ge> 3"
    by (metis Un_insert_right Un_upper2 assms(7) matroid_ax_2 order_trans sup_bot.right_neutral)
  have "{A,B,M,P} \<union> {C,D,M,P} = {A,B,C,D,M,P}"
    by auto 
  then have "rk {A,B,C,D,M,P} + rk {M,P} \<le> rk {A,B,M,P} + rk {C,D,M,P}"
    by (smt le_inf_iff matroid_ax_3_alt order_trans subset_insertI)
  then have i3:"rk {A,B,C,D,M,P} + rk {M,P} \<le> 4"
    using \<open>rk {A, B, M, P} = 2\<close> \<open>rk {C, D, M, P} = 2\<close> by linarith
  have i4:"rk {A,B,C,D,M,P} + rk {M,P} \<ge> 3 + rk{M,P}"
    by (simp add: \<open>3 \<le> rk {A, B, C, D, M, P}\<close>)
  from i3 and i4 show "rk {M,P} = 1"
    by (metis (no_types, lifting) \<open>rk {A, B, C, D, M, P} + rk {M, P} \<le> rk {A, B, M, P} + rk {C, D, M, P}\<close> \<open>rk {A, B, M, P} = 2\<close> \<open>rk {C, D, M, P} = 2\<close> add_le_cancel_left add_numeral_left antisym insert_absorb2 numeral_Bit1 numeral_One numeral_plus_one one_add_one one_le_numeral order_trans rk_ax_couple rk_ax_singleton)
qed

(* The following lemma allows to derive that there exists two lines that do not meet, i.e that belong
to two different planes *)
lemma rk_ax_dim_alt: "\<exists>A B C D. \<forall>M. rk {A,B,M} \<noteq> 2 \<or> rk {C,D,M} \<noteq> 2"
proof-
  obtain A B C D where f1:"rk {A,B,C,D} \<ge> 4"
  proof-
    assume a1:"\<And>A B C D. 4 \<le> rk {A, B, C, D} \<Longrightarrow> thesis"
    then show "thesis"
    proof-
      have "\<exists>X Y Z W. rk {X,Y,Z,W} \<ge> 4" by (simp add: rk_ax_dim)
      thus "thesis" using a1 by blast
    qed
  qed
  have "\<forall>M. rk {A,B,M} \<noteq> 2 \<or> rk {C,D,M} \<noteq> 2"
  proof
    fix M
    have "{A,B,C,D,M} = {A,B,M} \<union> {C,D,M}"
      by auto
    then have "rk {A,B,C,D,M} + rk {M} \<le> rk {A,B,M} + rk {C,D,M}"
      by (smt le_inf_iff matroid_ax_3_alt order_trans subset_insertI)
    then have "rk {A,B,C,D,M} \<le> 3" if "rk {A,B,M} = 2" and "rk {C,D,M} = 2"
      by (smt One_nat_def Suc_leI Suc_le_mono Suc_numeral add_Suc_right add_leD1 add_mono le_antisym not_le numeral_3_eq_3 numeral_One numeral_plus_one one_add_one rk_ax_singleton that(1) that(2))
    then have "rk {A,B,C,D} \<le> 3" if "rk {A,B,M} = 2" and "rk {C,D,M} = 2"
      by (smt insert_commute matroid_ax_2 order_trans subset_insertI that(1) that(2))
    thus "rk {A, B, M} \<noteq> 2 \<or> rk {C, D, M} \<noteq> 2 "
      using \<open>4 \<le> rk {A, B, C, D}\<close> by linarith
  qed
  thus "\<exists>A B C D. \<forall>M. rk {A, B, M} \<noteq> 2 \<or> rk {C, D, M} \<noteq> 2"
    by blast
qed












    



