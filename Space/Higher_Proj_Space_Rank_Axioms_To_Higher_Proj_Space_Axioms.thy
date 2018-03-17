theory Higher_Proj_Space_Rank_Axioms_To_Higher_Proj_Space_Axioms
  imports Main Higher_Projective_Space_Rank_Axioms
begin

(*
Contents:
- One proves that if the rank-based axioms are satisfied then the higher projective space axioms 
are satisfied
*)

(* Assume that we have a model of our rank-based axioms and prove this model is also a model of 
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

(* Next, we prove that the higher projective space axioms are satisfied *)





