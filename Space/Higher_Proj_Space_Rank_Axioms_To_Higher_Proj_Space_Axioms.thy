theory Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms
  imports Main Higher_Projective_Space_Rank_Axioms
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
"incid P l \<equiv> rk {fst l, snd l, P} = 2"

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
proof (rule allI, rule allI)
  fix P Q
  have f1:"incid P (Abs_lines (line P Q)) \<and> incid Q (Abs_lines (line P Q))" if "P \<noteq> Q"
    by (smt Abs_lines_inverse Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.fst_def Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.snd_def fst_pt.simps incid_def insert_commute mem_Collect_eq rk_triple_rep snd_pt.simps that)
  define l where "l = Abs_lines (line P (@ R. R \<noteq> P))"
  have f2:"incid P l \<and> incid Q l" if "P = Q"
    by (smt Abs_lines_induct Abs_lines_inverse Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.fst_def Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.snd_def fst_pt.simps incid_def insert_commute l_def mem_Collect_eq rk_triple_rep snd_pt.simps some_eq_ex that)
  from f1 and f2 show "\<exists>l. incid P l \<and> incid Q l" by blast
qed

definition line_eq :: "lines \<Rightarrow> lines \<Rightarrow> bool" where
"line_eq k l \<equiv> rk {fst k, snd k, fst l, snd l} = 2"

lemma line_eq_refl : "line_eq l l"
  by (metis (mono_tags, lifting) Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.fst_def Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms.snd_def Rep_lines insert_absorb2 insert_commute line_eq_def mem_Collect_eq rk_triple_rep)

lemma line_eq_sym : "line_eq k l = line_eq l k"
  by (simp add: insert_commute line_eq_def)

lemma line_eq_trans : "line_eq k l \<longrightarrow> line_eq l m \<longrightarrow> line_eq k m"


lemma ax1_uniqueness : "\<forall>P Q k l. 
(incid P k) \<longrightarrow> (incid Q k) \<longrightarrow> (incid P l) \<longrightarrow> (incid Q l) \<longrightarrow> (P = Q) \<or> (line_eq k l)"






