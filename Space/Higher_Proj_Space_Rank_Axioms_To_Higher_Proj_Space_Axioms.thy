theory Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms
  imports Main Higher_Projective_Space_Rank_Axioms Matroid_Rank_Properties
begin

(*
Contents:
- One proves that if the rank-based axioms are satisfied then the higher projective space axioms 
are satisfied
*)

(* Assume that we have a model of our rank-based axioms and prove that it is also a model of 
our higher projective space axioms *)

(* First, one has a type of points *)

type_synonym points = "Points"

(* Second, one has a type of lines *)

datatype Lines = line "Points" "Points"

fun fst_pt :: "Lines \<Rightarrow> points" where
"fst_pt (line A B) = A"

fun snd_pt :: "Lines \<Rightarrow> points" where
"snd_pt (line A B) = B"

typedef lines = "{l:: Lines. fst_pt l \<noteq> snd_pt l}"
proof-
  obtain A B where "rk {A,B} = 2"
    using rk_axiom_3_points by blast
  then have "A \<noteq> B"
    by (metis One_nat_def card.empty card_Suc_eq insert_absorb insert_absorb2 insert_not_empty matroid_ax_1b numeral_le_one_iff semiring_norm(69))
  thus "?thesis"
    by (metis (mono_tags) fst_pt.simps mem_Collect_eq snd_pt.simps)
qed

definition fst :: "lines \<Rightarrow> points" where
"fst l \<equiv> fst_pt (Rep_lines l)"

definition snd :: "lines \<Rightarrow> points" where
"snd l \<equiv> snd_pt (Rep_lines l)"

(* Next, we define an incidence relation between points and lines *)

definition incid :: "points \<Rightarrow> lines \<Rightarrow> bool" where
"incid P l \<equiv> rk {fst l, snd l, P} \<le> 2"

lemma incid_rk :
  assumes "incid P l"
  shows "rk {fst l, snd l, P} = 2"
proof-
  have "rk {fst l, snd l, P} \<ge> 2"
    by (metis (mono_tags, lifting) Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.fst_def Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.snd_def Rep_lines Un_insert_left Un_upper1 insert_is_Un matroid_ax_2 mem_Collect_eq rk_couple)
  thus "rk {fst l, snd l, P} = 2"
    using assms incid_def by auto
qed

(* Then we prove that the higher projective space axioms are satisfied *)

lemma rk_triple_rep : 
  assumes "P \<noteq> Q"
  shows "rk {P, P, Q} = 2"
proof-
  have f1:"rk {P, P, Q} \<ge> 2"
    by (simp add: assms rk_ax_couple)
  have f2:"rk {P, P, Q} \<le> 2"
    by (metis One_nat_def add.right_neutral add_Suc_right assms card.empty card_Suc_eq empty_iff insert_absorb2 insert_iff matroid_ax_1b one_add_one)
  from f1 and f2 show "rk {P, P, Q} = 2"
    using le_antisym by blast
qed
  
lemma ax1_existence : "\<forall>P Q.\<exists>l. (incid P l) \<and> (incid Q l)"
proof (rule allI)+
  fix P Q
  have f1:"incid P (Abs_lines (line P Q)) \<and> incid Q (Abs_lines (line P Q))" if "P \<noteq> Q"
    by (smt Abs_lines_inverse Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.fst_def Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.snd_def fst_pt.simps incid_def insert_commute mem_Collect_eq order_refl rk_triple_rep snd_pt.simps that)
  define l where "l = Abs_lines (line P (@ R. R \<noteq> P))"
  have f2:"incid P l \<and> incid Q l" if "P = Q"
    by (smt Abs_lines_induct Abs_lines_inverse Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.fst_def fst_pt.simps incid_def insert_absorb2 insert_commute l_def matroid_ax_2 mem_Collect_eq rk_triple_rep snd_pt.simps some_eq_ex subset_insertI that)
  from f1 and f2 show "\<exists>l. incid P l \<and> incid Q l" by blast
qed

definition line_eq :: "lines \<Rightarrow> lines \<Rightarrow> bool" where
"line_eq k l \<equiv> rk {fst k, snd k, fst l, snd l} \<le> 2"

lemma line_eq_rk :
  assumes "line_eq k l"
  shows "rk {fst k, snd k, fst l, snd l} = 2"
proof-
  have f1:"rk {fst k, snd k, fst l, snd l} \<le> 2"
    using assms line_eq_def by auto
  have "fst k \<noteq> snd k \<and> fst l \<noteq> snd l"
    using Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.fst_def Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.snd_def Rep_lines by auto
  then have f2:"rk {fst k, snd k, fst l, snd l} \<ge> 2"
    by (meson matroid_ax_2 order.trans rk_ax_couple subset_insertI)
  from f1 and f2 show "rk {fst k, snd k, fst l, snd l} = 2"
    using antisym_conv by auto
qed

lemma line_eq_refl : "line_eq l l"
  by (smt Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.fst_def Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.snd_def Rep_lines eq_iff insert_absorb2 insert_commute line_eq_def mem_Collect_eq rk_triple_rep)

lemma line_eq_sym : "line_eq k l = line_eq l k"
  by (simp add: insert_commute line_eq_def)

lemma line_eq_trans : "line_eq k l \<longrightarrow> line_eq l m \<longrightarrow> line_eq k m"
proof(rule impI)+
  assume "line_eq k l" and "line_eq l m"
  have "{fst l, snd l} \<subseteq> {fst k, snd k, fst l, snd l} \<inter> {fst l, snd l, fst m, snd m}" by auto
  then have "rk {fst k, snd k, fst l, snd l, fst m, snd m} + rk {fst l, snd l} \<le> 
    rk {fst k, snd k, fst l, snd l} + rk {fst l, snd l, fst m, snd m}" using matroid_ax_3_alt
    by (smt Un_insert_left le_infE sup.absorb_iff2)
  then have "rk {fst k, snd k, fst l, snd l, fst m, snd m} \<le> 2"
    by (metis Nat.le_diff_conv2 \<open>line_eq k l\<close> \<open>line_eq l m\<close> add_diff_cancel_right' add_leD2 insert_absorb2 line_eq_refl line_eq_rk rk_couple)
  then have "rk {fst k, snd k, fst m, snd m} \<le> 2" using matroid_ax_2 by (smt insert_commute order_trans subset_insertI)
  thus "line_eq k m"
    using line_eq_def by auto
qed

lemma ax1_uniqueness : "\<forall>P Q k l. 
(incid P k) \<longrightarrow> (incid Q k) \<longrightarrow> (incid P l) \<longrightarrow> (incid Q l) \<longrightarrow> (P = Q) \<or> (line_eq k l)"
proof-
  fix P Q k l
  assume "incid P k" and "incid Q k" and "incid P l" and "incid Q l"
  have "line_eq k l" if "P \<noteq> Q"
  proof-
    have f1:"rk {P, Q} = 2"
      by (simp add: rk_couple that)
    have f2:"rk {fst k, snd k, P, Q} = 2" using matroid_ax_3_alt'
      by (smt Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.fst_def Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.snd_def Rep_lines Un_insert_left \<open>incid P k\<close> \<open>incid Q k\<close> incid_rk insert_absorb2 insert_is_Un matroid_ax_2 mem_Collect_eq rk_triple_rep subset_insertI)
    have f3:"rk {fst l, snd l, P, Q} = 2" using matroid_ax_3_alt'
      by (smt Un_insert_right \<open>incid P l\<close> \<open>incid Q l\<close> incid_rk insert_absorb2 insert_commute line_eq_refl line_eq_rk sup_bot.right_neutral)
    have f4:"rk {fst k, snd k, fst l, snd l, P, Q} + rk {P, Q} \<le> rk {fst k, snd k, P, Q} + rk {fst l, snd l, P, Q}"
      using matroid_ax_3_alt[of "{P, Q}" "{fst k, snd k, P, Q}" "{fst l, snd l, P, Q}"]
      by (simp add: insert_commute)
    from f1 and f2 and f3 and f4 have "rk {fst k, snd k, fst l, snd l, P, Q} \<le> 2" by auto
    thus "line_eq k l" using matroid_ax_2 by (smt eq_iff f3 insert_mono insert_subset line_eq_def)
  qed
  show "P = Q \<or> line_eq k l"





