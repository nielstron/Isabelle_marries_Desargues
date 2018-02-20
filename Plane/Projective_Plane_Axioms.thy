theory Projective_Plane_Axioms
  imports Main
begin

(* Contents:
- We introduce the types of points and lines and an incidence relation between them.
- A set of axioms for the projective plane (the models of these axioms are 
n-dimensional with n \<ge> 2). 
*)

(** The Axioms of the Projective Plane **)

(* One has a type of points *)
typedecl "Points"

(* One has a type of lines *)
typedecl "Lines"

(* One has an incidence relation between points and lines *)
consts incid :: "Points \<Rightarrow> Lines \<Rightarrow> bool"

(* Ax1: Any two (distinct) points lie on a (unique) line *)
axiomatization where
ax1: "\<forall>P Q. \<exists>l. incid P l \<and> incid Q l"

(* Ax2: Any two (distinct) lines meet in a (unique) point *)
axiomatization where
ax2: "\<forall>l m. \<exists>P. incid P l \<and> incid P m"

(* The uniqueness part *)
axiomatization where
ax_uniqueness: "\<forall>P Q l m. incid P l \<longrightarrow> incid Q l \<longrightarrow> incid P m \<longrightarrow> incid Q m \<longrightarrow>
P = Q \<or> l = m"

definition distinct4 :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> bool" where
"distinct4 A B C D \<equiv> (A \<noteq> B) \<and> (A \<noteq> C) \<and> (A \<noteq> D) \<and> (B \<noteq> C) \<and> (B \<noteq> D) \<and> (C \<noteq> D)"

(* Ax3: There exists four points such that no three of them are collinear *)
axiomatization where 
ax3: "\<exists>A B C D. distinct4 A B C D \<and> (\<forall>l. 
(incid A l \<and> incid B l \<longrightarrow> \<not>(incid C l) \<and> \<not>(incid D l)) \<and>
(incid A l \<and> incid C l \<longrightarrow> \<not>(incid B l) \<and> \<not>(incid D l)) \<and>
(incid A l \<and> incid D l \<longrightarrow> \<not>(incid B l) \<and> \<not>(incid C l)) \<and>
(incid B l \<and> incid C l \<longrightarrow> \<not>(incid A l) \<and> \<not>(incid D l)) \<and>
(incid B l \<and> incid D l \<longrightarrow> \<not>(incid A l) \<and> \<not>(incid C l)) \<and>
(incid C l \<and> incid D l \<longrightarrow> \<not>(incid A l) \<and> \<not>(incid B l)))"

(* Biblio.:
- Nicolas Magaud, Julien Narboux, Pascal Schreck; coq-projective-geometry; code available at
https://github.com/coq-contribs/projective-geometry  *)



end