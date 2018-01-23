theory Pappus_Property
  imports Main Projective_Plane_Axioms
begin

definition col :: "[points, points, points] \<Rightarrow> bool" where
"col A B C \<equiv> \<exists>l. incid A l \<and> incid B l \<and> incid C l"

definition distinct6 ::
  "[points, points, points, points, points, points] \<Rightarrow> bool" where
"distinct6 A B C D E F \<equiv> (A \<noteq> B) \<and> (A \<noteq> C) \<and> (A \<noteq> D) \<and> (A \<noteq> E) \<and> (A \<noteq> F) \<and>
(B \<noteq> C) \<and> (B \<noteq> D) \<and> (B \<noteq> E) \<and> (B \<noteq> F) \<and>
(C \<noteq> D) \<and> (C \<noteq> E) \<and> (C \<noteq> F) \<and>
(D \<noteq> E) \<and> (D \<noteq> F) \<and>
(E \<noteq> F)"

definition line :: "points \<Rightarrow> points \<Rightarrow> lines set" where
"line P Q \<equiv> {l. incid P l \<and> incid Q l}"

lemma uniq_line:
  assumes a1:"P \<noteq> Q" and a2:"l \<in> line P Q" and a3:"m \<in> line P Q"
  shows "l = m"
  using a1 a2 a3 ax_uniqueness line_def by blast

(* The point P is the intersection of the lines AB and CD. For P to be well-defined,
A and B should be distinct, C and D should be distinct, and the lines AB and CD should
be distinct *)
definition is_a_proper_intersec :: "[points, points, points, points, points] \<Rightarrow> bool" where
"is_a_proper_intersec P A B C D \<equiv> col P A B \<and> col P C D \<and> (A \<noteq> B) \<and> (C \<noteq> D) \<and>
(line A B \<noteq> line C D)"

(* We state a first form of Pappus's property *)
definition pappus1 :: 
"[points, points, points, points, points, points, points, points, points] => bool " where
"pappus1 A B C A' B' C' P Q R \<equiv> 
  col A B C \<longrightarrow> col A' B' C' \<longrightarrow> distinct6 A B C A' B' C'
    \<longrightarrow> is_a_proper_intersec P A B' A' B \<longrightarrow> is_a_proper_intersec Q B C' B' C \<longrightarrow>
      is_a_proper_intersec R A C' A' C \<longrightarrow> col P Q R"

definition is_a_intersec :: "[points, points, points, points, points] \<Rightarrow> bool" where
"is_a_intersec P A B C D \<equiv> col P A B \<and> col P C D"

(* We state a second form of Pappus's property *)
definition pappus2 ::
"[points, points, points, points, points, points, points, points, points] \<Rightarrow> bool" where
"pappus2 A B C A' B' C' P Q R \<equiv> 
  distinct6 A B C A' B' C' \<or> (A \<noteq> B' \<and> A'\<noteq> B \<and> line A B' \<noteq> line A' B \<and> 
    B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
      A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C) \<longrightarrow> 
        col A B C \<longrightarrow> col A' B' C' \<longrightarrow> is_a_intersec P A B' A' B \<longrightarrow> 
          is_a_intersec Q B C' B' C \<longrightarrow> is_a_intersec R A C' A' C 
            \<longrightarrow> col P Q R"

definition meet_in :: "lines \<Rightarrow> lines \<Rightarrow> points \<Rightarrow> bool" where
"meet_in l m P \<equiv> incid P l \<and> incid P m"

lemma uniq_meet_in:
  assumes a1:"l \<noteq> m" and a2:"meet_in l m P" and a3:"meet_in l m Q"
  shows "P = Q"
  using a1 a2 a3 ax_uniqueness meet_in_def by blast

(* The first and the second forms of Pappus's property are equivalent *)
lemma pappus21:
  assumes "pappus2 A B C A' B' C' P Q R"
  shows "pappus1 A B C A' B' C' P Q R"
  using assms is_a_intersec_def is_a_proper_intersec_def pappus1_def pappus2_def by auto

lemma is_a_proper_intersec_is_a_intersec:
  assumes "is_a_proper_intersec P A B C D"
  shows "is_a_intersec P A B C D"
  using assms is_a_intersec_def is_a_proper_intersec_def by auto

lemma towards_pappus12:
  assumes a0:"pappus1 A B C A' B' C' P Q R"
  and a1:"distinct6 A B C A' B' C'"
  and a2:"col A B C" 
  and a3:"col A' B' C'" 
  and a4:"is_a_intersec P A B' A' B"
  and a5:"is_a_intersec Q B C' B' C" 
  and a6:"is_a_intersec R A C' A' C"
  shows "col P Q R"
proof - 
  have "col P Q R" when "line A B' = line A' B"
    by (smt CollectD CollectI ax_uniqueness bexI col_def distinct6_def a1 a2 a4 a5 a6 is_a_intersec_def line_def that)
  have "col P Q R" when "line B C' = line B' C"
    by (smt CollectD CollectI ax_uniqueness col_def distinct6_def a1 a3 a4 a5 a6 is_a_intersec_def line_def that)
  have "col P Q R" when "line A C' = line A' C"
    by (smt CollectD CollectI ax_uniqueness bexI col_def distinct6_def a1 a2 a3 a4 a5 a6 is_a_intersec_def line_def mem_Collect_eq that)
  have "col P Q R" when "line A B' \<noteq> line A' B \<and> line B C' \<noteq> line B' C \<and> line A C' \<noteq> line A' C"
    using \<open>line A B' = line A' B \<Longrightarrow> col P Q R\<close> \<open>line A C' = line A' C \<Longrightarrow> col P Q R\<close> \<open>line B C' = line B' C \<Longrightarrow> col P Q R\<close> a1 a2 a3 a4 a5 a6 assms distinct6_def is_a_intersec_def is_a_proper_intersec_def pappus1_def by auto
  show "col P Q R"
    using \<open>line A B' = line A' B \<Longrightarrow> col P Q R\<close> \<open>line A B' \<noteq> line A' B \<and> line B C' \<noteq> line B' C \<and> line A C' \<noteq> line A' C \<Longrightarrow> col P Q R\<close> \<open>line A C' = line A' C \<Longrightarrow> col P Q R\<close> \<open>line B C' = line B' C \<Longrightarrow> col P Q R\<close> by linarith
qed

lemma pappus12:
  assumes "pappus1 A B C A' B' C' P Q R"
  shows "pappus2 A B C A' B' C' P Q R"
  using assms pappus2_def towards_pappus12 by (smt ax1 ax_uniqueness col_def distinct6_def is_a_intersec_def)

lemma pappus1_iff_pappus2: 
"pappus1 A B C A' B' C' P Q R \<equiv> pappus2 A B C A' B' C' P Q R"
  by (smt pappus12 pappus21)


  

   