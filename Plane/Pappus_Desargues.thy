theory Pappus_Desargues
  imports Main Projective_Plane_Axioms Pappus_Property Pascal_Property Desargues_Property
begin

lemma col_ABC_ABD_1:
  assumes "A \<noteq> B" and "col A B C" and "col A B D"
  shows "col B C D"
  by (metis assms(1) assms(2) assms(3) ax_uniqueness col_def)

lemma col_ABC_ABD_2:
  assumes "A \<noteq> B" and "col A B C" and "col A B D"
  shows "col A C D"
  by (metis assms(1) assms(2) assms(3) ax_uniqueness col_def)

lemma col_line_eq_1:
  assumes "A \<noteq> B" and "B \<noteq> C"and "col A B C"
  shows "line A B = line B C"
  by (metis assms(1) assms(2) assms(3) ax_uniqueness col_def incidA_lAB incidB_lAB)

lemma col_line_eq_2:
  assumes "A \<noteq> B" and "A \<noteq> C" and "col A B C"
  shows "line A B = line A C"
  by (metis assms(1) assms(2) assms(3) col_line_eq_1 col_rot_CW line_comm)

lemma desargues_config_not_col_1: 
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col A A' B'"
proof
  assume a1:"col A A' B'"
  have f1:"A \<noteq> A'" using assms desargues_config_def distinct7_def by blast
  have f2:"col A A' R"
    using assms desargues_config_def meet_3_col_1 by blast
  from f1 and f2 and a1 have f3:"col A' B' R"
    using col_ABC_ABD_1 by blast
  from a1 have f4:"line A A' = line A' B'"
    by (metis assms ax_uniqueness col_def desargues_config_def f1 incidA_lAB incidB_lAB)
  have f5:"A' \<noteq> B'" using assms desargues_config_def distinct7_def by blast
  have f6:"B' \<noteq> R" using assms desargues_config_def distinct7_def by blast
  from f3 and f5 and f6 have f7:"line A' B' = line B' R"
    using col_line_eq_1 by blast
  have "line B' R = line B B'"
    by (metis a1 assms col_2cycle col_AAB col_line_eq_1 desargues_config_def f6 meet_3_col_2)
  have "line A A' = line B B'"
    by (simp add: \<open>line B' R = line B B'\<close> f4 f7)
  then have "False"
    using assms desargues_config_def distinct3l_def by auto
  then show f8:"col A A' B' \<Longrightarrow> False"
    by simp
qed

lemma desargues_config_not_col_2:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col B B' C'"
  using assms desargues_config_not_col_1 desargues_config_rot_CCW by blast

lemma desargues_config_not_col_3:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col C C' B'"
  by (smt assms col_line_eq_1 col_rot_CW desargues_config_def desargues_config_not_col_2 desargues_config_rot_CW distinct3l_def meet_3_in_def meet_col_1 meet_col_2)

lemma desargues_config_not_col_4:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col A A' C'"
  using assms desargues_config_not_col_3 desargues_config_rot_CCW by blast

lemma desargues_config_not_col_5:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col B B' A'"
  using assms desargues_config_not_col_3 desargues_config_rot_CW by blast

lemma desargues_config_not_col_6:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col C C' A'"
  using assms desargues_config_not_col_1 desargues_config_rot_CW by blast

lemma desargues_config_not_col_7:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col A B B'"
proof
  assume a1:"col A B B'"
  have f1:"col A B R"
    by (metis a1 assms col_ABB col_ABC_ABD_2 col_rot_CW desargues_config_def desargues_config_not_col_5 meet_3_col_2)
  have f2:"col A A' R"
    using assms desargues_config_def meet_3_col_1 by blast
  have f3:"A \<noteq> A'"
    using assms col_AAB desargues_config_not_col_4 by blast
  have f4:"A \<noteq> R" using assms desargues_config_def distinct7_def by auto
  from f2 and f3 and f4 have f5:"line A A' = line A R"
    using col_line_eq_2 by blast
  from f1 have f6:"line A R = line B R"
    by (metis a1 assms col_2cycle col_ABC_ABD_2 desargues_config_not_col_1 f2 f4)
  have f7:"line B R = line B B'"
    by (metis \<open>line A R = line B R\<close> a1 assms col_AAB col_line_eq_1 desargues_config_def desargues_config_not_col_2 f1)
  from f5 and f6 and f7 have "line A A' = line B B'"
    by simp
  then have "False"
    using assms desargues_config_def distinct3l_def by auto
  thus "col A B B' \<Longrightarrow> False"
    by simp
qed

lemma desargues_config_not_col_8:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col A C C'"
  by (metis assms col_ABA col_line_eq_1 col_rot_CW desargues_config_def desargues_config_not_col_3 desargues_config_not_col_7 distinct3l_def meet_3_col_1 meet_3_col_2 meet_3_col_3)

lemma desargues_config_not_col_9:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col B A A'"
  using assms desargues_config_not_col_8 desargues_config_rot_CCW by blast
 
lemma desargues_config_not_col_10:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col B C C'"
  using assms desargues_config_not_col_7 desargues_config_rot_CCW by blast

lemma desargues_config_not_col_11:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col C A A'"
  using assms desargues_config_not_col_7 desargues_config_rot_CW by blast
 
lemma desargues_config_not_col_12:
  assumes "desargues_config A B C A' B' C' M N P R"
  shows "\<not> col C B B'"
  using assms desargues_config_not_col_8 desargues_config_rot_CW by blast

lemma col_inter:
  assumes "A \<noteq> C" and "B \<noteq> C" and "col A B C"
  shows "inter l (line B C) = inter l (line A C)"
  by (metis assms(1) assms(2) assms(3) col_line_eq_1 col_line_eq_2)

lemma lemma_1:
  assumes "desargues_config A B C A' B' C' M N P R" and "is_pappus"
  shows "col M N P \<or> incid A (line B' C') \<or> incid C' (line A B)"
proof-
  assume "\<not> incid A (line B' C')" and "\<not> incid C' (line A B)"
(* The proof consists in three successive applications of Pappus property *)
  define Q E X F where "Q = inter (line A B) (line B' C')" and "E = inter (line A C) (line R Q)"
    and "X = inter (line A C') (line R B)" and "F = inter (line A' C') (line R Q)"
  have "col X E M"
  proof-
    have f1:"distinct6 C C' R Q B A"
      by (smt Q_def \<open>\<not> incid A (line B' C')\<close> \<open>\<not> incid C' (line A B)\<close> assms(1) col_ABB col_A_B_ABl col_A_B_lAB col_line_eq_2 col_rot_CW desargues_config_def desargues_config_not_col_12 desargues_config_not_col_2 desargues_config_not_col_3 desargues_config_not_col_7 desargues_config_not_col_9 distinct6_def incidA_lAB line_comm meet_3_col_1 meet_3_col_2) 
    have f2: "col C C' R"
      using assms(1) desargues_config_def meet_3_col_3 by blast
    have f3: "col Q B A"
      using Q_def col_2cycle col_A_B_ABl col_rot_CW by blast
    have f4: "is_a_intersec E C A Q R"
      using E_def col_2cycle inter_is_a_intersec is_a_intersec_def by auto
    have f5:"is_a_intersec M C B Q C'"
      by (metis Q_def assms(1) col_2cycle col_ABB col_ABC_ABD_1 col_A_B_lAB col_rot_CW desargues_config_def is_a_intersec_def meet_col_1 meet_col_2)
    have f6:"is_a_intersec X C' A B R"
      using X_def col_2cycle inter_is_a_intersec is_a_intersec_def by auto
    from f1 and f2 and f3 and f4 and f5 and f6 have "col M X E"
      using assms(2) is_pappus2_def is_pappus_def by blast
    then show "col X E M"
      using col_def by auto
  qed
  have "col P X F"
  proof-
    have f1:"distinct6 A' A R Q B' C'"
      by (smt Q_def \<open>\<not> incid A (line B' C')\<close> \<open>\<not> incid C' (line A B)\<close> assms(1) col_AAB col_A_B_ABl col_A_B_lAB col_line_eq_1 col_rot_CW desargues_config_def desargues_config_not_col_2 desargues_config_not_col_3 desargues_config_not_col_4 desargues_config_not_col_6 desargues_config_not_col_7 distinct6_def incidB_lAB meet_3_col_2 meet_3_col_3)
    have f2:"col A' A R"
      by (metis assms(1) col_ABA col_line_eq_1 desargues_config_def meet_3_col_1)
    have f3:"col Q B' C'"
      by (simp add: Q_def col_A_B_lAB col_rot_CW)
    have "is_a_intersec (inter (line A B) (line A' B')) A' B' Q A"
      by (metis Q_def col_def incidA_lAB incid_inter_left inter_is_a_intersec is_a_intersec_def)
    then have f4:"is_a_intersec P A' B' Q A"
      using assms(1) desargues_config_def meet_in_def uniq_inter by auto
    have f5:"is_a_intersec X A C' B' R"
      by (metis X_def assms(1) col_def col_line_eq_2 desargues_config_def desargues_config_not_col_9 f2 inter_is_a_intersec is_a_intersec_def line_comm meet_3_col_2)
    have f6:"is_a_intersec F A' C' Q R"
      by (metis F_def inter_is_a_intersec inter_line_line_comm)
    from f1 and f2 and f3 and f4 and f5 and f6 and assms(2) 
      show "col P X F"
        using is_pappus2_def is_pappus_def by blast
    qed
    have "col M N P"
    proof-
      have f1:"Q \<noteq> C' \<and> X \<noteq> E \<and> line Q C' \<noteq> line X E"
        by (smt E_def Q_def X_def \<open>\<not> incid A (line B' C')\<close> \<open>\<not> incid C' (line A B)\<close> assms(1) col_ABB col_A_B_ABl col_A_B_lAB col_line_eq_2 col_rot_CW desargues_config_def desargues_config_not_col_10 desargues_config_not_col_2 desargues_config_not_col_8 incidB_lAB incid_C_AB line_comm meet_3_col_1 meet_3_col_2 meet_3_col_3) 
      have f2:"E \<noteq> A \<and> C' \<noteq> F \<and> line E A \<noteq> line C' F"
        by (smt F_def Q_def X_def \<open>Q \<noteq> C' \<and> X \<noteq> E \<and> line Q C' \<noteq> line X E\<close> \<open>col X E M\<close> assms(1) ax_uniqueness col_A_B_ABl col_A_B_lAB col_def col_line_eq_1 desargues_config_def desargues_config_not_col_10 desargues_config_not_col_2 desargues_config_not_col_3 incidA_lAB incid_inter_right meet_3_col_3 meet_all_3 meet_in_def)
      have f3:"Q \<noteq> A \<and> X \<noteq> F \<and> line Q A \<noteq> line X F"
        by (smt F_def Q_def X_def \<open>\<not> incid A (line B' C')\<close> \<open>\<not> incid C' (line A B)\<close> assms(1) ax_uniqueness col_def desargues_config_def desargues_config_not_col_10 desargues_config_not_col_2 desargues_config_not_col_7 incidA_lAB incidB_lAB incid_inter_left incid_inter_right meet_3_col_2 meet_3_col_3)
      have f4:"col Q E F"
        using E_def F_def col_def incidB_lAB incid_inter_right by blast
      have f5:"col X C' A"
        using X_def col_2cycle col_A_B_ABl col_rot_CW by blast
      have f6:"is_a_intersec M Q C' X E"
        using Q_def \<open>col X E M\<close> assms(1) col_def desargues_config_def incidB_lAB incid_inter_right is_a_intersec_def meet_in_def by auto
      have f7:"is_a_intersec N E A C' F"
        by (metis E_def F_def assms(1) ax_uniqueness col_rot_CW desargues_config_def f2 incidA_lAB incidB_lAB incid_inter_left is_a_intersec_def meet_col_1 meet_col_2)
      have f8:"is_a_intersec P Q A X F"
        by (smt Q_def \<open>col P X F\<close> assms(1) col_AAB col_A_B_ABl col_line_eq_2 desargues_config_def f3 incidA_lAB inter_is_a_intersec line_comm meet_in_def uniq_inter)
      from f1 and f2 and f3 and f4 and f5 and f6 and f7 and f8 and assms(2) show "col M N P"
        using is_pappus2_def is_pappus_def by blast
    qed









