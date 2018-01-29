theory Pappus_Property
  imports Main Projective_Plane_Axioms
begin

(* Contents:
- We give two formulations of Pappus's property for a plane [is_pappus1] [is_pappus2].
- We prove the equivalence of these two formulations [pappus_equiv]. 
*)

definition col :: "[Points, Points, Points] \<Rightarrow> bool" where
"col A B C \<equiv> \<exists>l. incid A l \<and> incid B l \<and> incid C l"

definition distinct6 ::
  "[Points, Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"distinct6 A B C D E F \<equiv> (A \<noteq> B) \<and> (A \<noteq> C) \<and> (A \<noteq> D) \<and> (A \<noteq> E) \<and> (A \<noteq> F) \<and>
(B \<noteq> C) \<and> (B \<noteq> D) \<and> (B \<noteq> E) \<and> (B \<noteq> F) \<and>
(C \<noteq> D) \<and> (C \<noteq> E) \<and> (C \<noteq> F) \<and>
(D \<noteq> E) \<and> (D \<noteq> F) \<and>
(E \<noteq> F)"

definition lines :: "Points \<Rightarrow> Points \<Rightarrow> Lines set" where
"lines P Q \<equiv> {l. incid P l \<and> incid Q l}"

lemma uniq_line:
  assumes "P \<noteq> Q" and "l \<in> lines P Q" and "m \<in> lines P Q"
  shows "l = m"
  using assms(1) assms(2) assms(3) lines_def ax_uniqueness by blast

definition line :: "Points \<Rightarrow> Points \<Rightarrow> Lines" where
"line P Q \<equiv> @l. incid P l \<and> incid Q l"


(* The point P is the intersection of the lines AB and CD. For P to be well-defined,
A and B should be distinct, C and D should be distinct, and the lines AB and CD should
be distinct *)
definition is_a_proper_intersec :: "[Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"is_a_proper_intersec P A B C D \<equiv> (A \<noteq> B) \<and> (C \<noteq> D) \<and> (line A B \<noteq> line C D)
\<and> col P A B \<and> col P C D"

(* We state a first form of Pappus's property *)
definition is_pappus1 :: 
"[Points, Points, Points, Points, Points, Points, Points, Points, Points] => bool " where
"is_pappus1 A B C A' B' C' P Q R \<equiv> 
  distinct6 A B C A' B' C' \<longrightarrow> col A B C \<longrightarrow> col A' B' C'
  \<longrightarrow> is_a_proper_intersec P A B' A' B \<longrightarrow> is_a_proper_intersec Q B C' B' C
  \<longrightarrow> is_a_proper_intersec R A C' A' C 
  \<longrightarrow> col P Q R"

definition is_a_intersec :: "[Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"is_a_intersec P A B C D \<equiv> col P A B \<and> col P C D"

(* We state a second form of Pappus's property *)
definition is_pappus2 ::
"[Points, Points, Points, Points, Points, Points, Points, Points, Points] \<Rightarrow> bool" where
"is_pappus2 A B C A' B' C' P Q R \<equiv> 
  (distinct6 A B C A' B' C' \<or> (A \<noteq> B' \<and> A'\<noteq> B \<and> line A B' \<noteq> line A' B \<and> 
  B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
  A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C)) 
  \<longrightarrow> col A B C \<longrightarrow> col A' B' C' \<longrightarrow> is_a_intersec P A B' A' B 
  \<longrightarrow> is_a_intersec Q B C' B' C \<longrightarrow> is_a_intersec R A C' A' C 
  \<longrightarrow> col P Q R"

lemma is_a_proper_intersec_is_a_intersec:
  assumes "is_a_proper_intersec P A B C D"
  shows "is_a_intersec P A B C D"
  using assms is_a_intersec_def is_a_proper_intersec_def by auto

(* The first and the second forms of Pappus's property are equivalent *)
lemma pappus21:
  assumes "is_pappus2 A B C A' B' C' P Q R"
  shows "is_pappus1 A B C A' B' C' P Q R"
  using assms is_pappus2_def is_pappus1_def is_a_proper_intersec_is_a_intersec by auto

lemma col_AAB: "col A A B"
  by (simp add: ax1 col_def)

lemma col_ABA: "col A B A"
  using ax1 col_def by blast

lemma col_ABB: "col A B B"
  by (simp add: ax1 col_def)

lemma incidA_lAB: "incid A (line A B)"
  by (metis (no_types, lifting) ax1 line_def someI_ex)

lemma incidB_lAB: "incid B (line A B)"
  by (metis (no_types, lifting) ax1 line_def someI_ex)

lemma degenerate_hexagon_is_pappus:
  assumes "distinct6 A B C A' B' C'" and "col A B C" and "col A' B' C'" and
"is_a_intersec P A B' A' B" and "is_a_intersec Q B C' B' C" and "is_a_intersec R A C' A' C"
and "line A B' = line A' B \<or> line B C' = line B' C \<or> line A C' = line A' C"
  shows "col P Q R"
proof -
  have "col P Q R" if "line A B' = line A' B"
  proof -
obtain ll :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Lines" where
"\<forall>x0 x1 x2. (\<exists>v3. incid x2 v3 \<and> incid x1 v3 \<and> incid x0 v3) = (incid x2 (ll x0 x1 x2) \<and> incid x1 (ll x0 x1 x2) \<and> incid x0 (ll x0 x1 x2))"
  by moura
  then have f1: "\<forall>p pa pb. (\<not> col p pa pb \<or> incid p (ll pb pa p) \<and> incid pa (ll pb pa p) \<and> incid pb (ll pb pa p)) \<and> (col p pa pb \<or> (\<forall>l. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid pb l))"
    using col_def by auto
  have f2: "\<forall>p pa pb pc pd. is_a_intersec p pa pb pc pd = (col p pa pb \<and> col p pc pd)"
    using is_a_intersec_def by blast
  then have f3: "incid P (ll B A' P) \<and> incid A' (ll B A' P) \<and> incid B (ll B A' P)"
    using f1 assms(4) by presburger
  have f4: "\<forall>p pa l la. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid p la \<or> \<not> incid pa la \<or> p = pa \<or> l = la"
    using ax_uniqueness by satx
  have f5: "A \<noteq> B \<and> A \<noteq> C \<and> A \<noteq> A' \<and> A \<noteq> B' \<and> A \<noteq> C' \<and> B \<noteq> C \<and> B \<noteq> A' \<and> B \<noteq> B' \<and> B \<noteq> C' \<and> C \<noteq> A' \<and> C \<noteq> B' \<and> C \<noteq> C' \<and> A' \<noteq> B' \<and> A' \<noteq> C' \<and> B' \<noteq> C'"
    using assms(1) distinct6_def by auto
have f6: "incid Q (ll C' B Q) \<and> incid B (ll C' B Q) \<and> incid C' (ll C' B Q)"
  using f2 f1 assms(5) by presburger
have f7: "incid A' (ll C' B' A') \<and> incid B' (ll C' B' A') \<and> incid C' (ll C' B' A')"
using f1 assms(3) by blast
  then have f8: "incid Q (line A' B)"
    using f6 f5 f4 by (metis incidA_lAB incidB_lAB that)
  have "incid R (ll C' A R) \<and> incid A (ll C' A R) \<and> incid C' (ll C' A R)"
    using f2 f1 assms(6) by presburger
  then have "incid R (line A' B)"
    using f7 f5 f4 by (metis incidA_lAB incidB_lAB that)
  then show ?thesis
    using f8 f5 f4 f3 f1 by (metis (no_types) incidA_lAB incidB_lAB)
  qed  
  have "col P Q R" if "line B C' = line B' C"
  proof -
have f1: "A \<noteq> B \<and> A \<noteq> C \<and> A \<noteq> A' \<and> A \<noteq> B' \<and> A \<noteq> C' \<and> B \<noteq> C \<and> B \<noteq> A' \<and> B \<noteq> B' \<and> B \<noteq> C' \<and> C \<noteq> A' \<and> C \<noteq> B' \<and> C \<noteq> C' \<and> A' \<noteq> B' \<and> A' \<noteq> C' \<and> B' \<noteq> C'"
  using assms(1) distinct6_def by auto
  obtain ll :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Lines" where
    f2: "\<forall>x0 x1 x2. (\<exists>v3. incid x2 v3 \<and> incid x1 v3 \<and> incid x0 v3) = (incid x2 (ll x0 x1 x2) \<and> incid x1 (ll x0 x1 x2) \<and> incid x0 (ll x0 x1 x2))"
    by moura
  then have f3: "incid A (ll C B A) \<and> incid B (ll C B A) \<and> incid C (ll C B A)"
    using assms(2) col_def by auto
  have "incid A' (ll C' B' A') \<and> incid B' (ll C' B' A') \<and> incid C' (ll C' B' A')"
    using f2 assms(3) col_def by force
  then show ?thesis
    using f3 f1 by (metis \<open>line A B' = line A' B \<Longrightarrow> col P Q R\<close> ax_uniqueness incidA_lAB incidB_lAB that)
  qed
  have "col P Q R" if "line A C' = line A' C"
  proof -
have f1: "A \<noteq> B \<and> A \<noteq> C \<and> A \<noteq> A' \<and> A \<noteq> B' \<and> A \<noteq> C' \<and> B \<noteq> C \<and> B \<noteq> A' \<and> B \<noteq> B' \<and> B \<noteq> C' \<and> C \<noteq> A' \<and> C \<noteq> B' \<and> C \<noteq> C' \<and> A' \<noteq> B' \<and> A' \<noteq> C' \<and> B' \<noteq> C'"
  using assms(1) distinct6_def by force
  obtain ll :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Lines" where
    f2: "\<forall>x0 x1 x2. (\<exists>v3. incid x2 v3 \<and> incid x1 v3 \<and> incid x0 v3) = (incid x2 (ll x0 x1 x2) \<and> incid x1 (ll x0 x1 x2) \<and> incid x0 (ll x0 x1 x2))"
    by moura
  then have f3: "incid A (ll C B A) \<and> incid B (ll C B A) \<and> incid C (ll C B A)"
    using assms(2) col_def by force
  have f4: "incid A (line A' C)"
    by (metis (no_types) incidA_lAB that)
  have f5: "incid A' (ll C' B' A') \<and> incid B' (ll C' B' A') \<and> incid C' (ll C' B' A')"
    using f2 assms(3) col_def by force
  have "incid C' (line A' C)"
by (metis (no_types) incidB_lAB that)
  then show ?thesis
using f5 f4 f3 f1 by (metis (no_types) \<open>line A B' = line A' B \<Longrightarrow> col P Q R\<close> ax_uniqueness incidA_lAB incidB_lAB)
qed
  show "col P Q R"
    using \<open>line A B' = line A' B \<Longrightarrow> col P Q R\<close> \<open>line A C' = line A' C \<Longrightarrow> col P Q R\<close> \<open>line B C' = line B' C \<Longrightarrow> col P Q R\<close> assms(7) by blast
qed

lemma pappus12:
  assumes "is_pappus1 A B C A' B' C' P Q R"
  shows "is_pappus2 A B C A' B' C' P Q R"
proof -
  have "col P Q R" if "(A \<noteq> B' \<and> A'\<noteq> B \<and> line A B' \<noteq> line A' B \<and> 
  B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> 
  A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C)" and "col A B C" and "col A' B' C'"
and "is_a_intersec P A B' A' B" and "is_a_intersec Q B C' B' C" 
and "is_a_intersec R A C' A' C" for A B C A' B' C' P Q R
  proof -
    have "col P Q R" if "A = B"
    proof -
      have "P = A"
        by (metis \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec P A B' A' B\<close> ax_uniqueness col_def incidA_lAB incidB_lAB is_a_intersec_def that)
      have "col P A C' \<and> col Q A C' \<and> col R A C'"
        using \<open>P = A\<close> \<open>is_a_intersec Q B C' B' C\<close> \<open>is_a_intersec R A C' A' C\<close> col_AAB is_a_intersec_def that by auto
      then show "col P Q R"
      proof -
obtain ll :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Lines" where
  "\<forall>x0 x1 x2. (\<exists>v3. incid x2 v3 \<and> incid x1 v3 \<and> incid x0 v3) = (incid x2 (ll x0 x1 x2) \<and> incid x1 (ll x0 x1 x2) \<and> incid x0 (ll x0 x1 x2))"
by moura
  then have f1: "\<forall>p pa pb. (\<not> col p pa pb \<or> incid p (ll pb pa p) \<and> incid pa (ll pb pa p) \<and> incid pb (ll pb pa p)) \<and> (col p pa pb \<or> (\<forall>l. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid pb l))"
    using col_def by auto
  have f2: "(\<forall>p pa pb. (\<not> col p pa pb \<or> incid p (ll pb pa p) \<and> incid pa (ll pb pa p) \<and> incid pb (ll pb pa p)) \<and> (col p pa pb \<or> (\<forall>l. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid pb l))) = (\<forall>p pa pb. (\<not> col p pa pb \<or> incid p (ll pb pa p) \<and> incid pa (ll pb pa p) \<and> incid pb (ll pb pa p)) \<and> (col p pa pb \<or> (\<forall>l. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid pb l)))"
    by meson
  have f3: "incid R (ll C' A R) \<and> incid A (ll C' A R) \<and> incid C' (ll C' A R)"
    using f1 \<open>col P A C' \<and> col Q A C' \<and> col R A C'\<close> by presburger
  have f4: "incid P (ll C' A P) \<and> incid A (ll C' A P) \<and> incid C' (ll C' A P)"
    using f1 \<open>col P A C' \<and> col Q A C' \<and> col R A C'\<close> by blast
  have f5: "ll C' A P = ll C' A Q"
    using f1 by (meson \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>col P A C' \<and> col Q A C' \<and> col R A C'\<close> ax_uniqueness)
  then have "incid R (ll C' A Q)"
    using f4 f3 by (metis (no_types) \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness)
  then show ?thesis
    using f5 f2 f1 by (metis \<open>col P A C' \<and> col Q A C' \<and> col R A C'\<close>)
    qed
  qed
  have "col P Q R" if "A = C" (* case where P = A = C = Q and P,Q,R belong to AB' *)
  proof -
    have "R = A"
      by (metis \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec R A C' A' C\<close> ax_uniqueness col_def incidA_lAB incidB_lAB is_a_intersec_def that)
    have "R = C"
      by (simp add: \<open>R = A\<close> that)
    have "col P A B' \<and> col Q A B' \<and> col R A B'"
      using \<open>R = A\<close> \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec Q B C' B' C\<close> col_def is_a_intersec_def that by auto
    then show "col P Q R"
    proof -
obtain ll :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Lines" where
"\<forall>x0 x1 x2. (\<exists>v3. incid x2 v3 \<and> incid x1 v3 \<and> incid x0 v3) = (incid x2 (ll x0 x1 x2) \<and> incid x1 (ll x0 x1 x2) \<and> incid x0 (ll x0 x1 x2))"
by moura
then have f1: "\<forall>p pa pb. (\<not> col p pa pb \<or> incid p (ll pb pa p) \<and> incid pa (ll pb pa p) \<and> incid pb (ll pb pa p)) \<and> (col p pa pb \<or> (\<forall>l. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid pb l))"
  using col_def by auto
then have f2: "incid R (ll B' A R) \<and> incid A (ll B' A R) \<and> incid B' (ll B' A R)"
    using \<open>col P A B' \<and> col Q A B' \<and> col R A B'\<close> by blast
  have f3: "incid P (ll B' A P) \<and> incid A (ll B' A P) \<and> incid B' (ll B' A P)"
    using f1 \<open>col P A B' \<and> col Q A B' \<and> col R A B'\<close> by presburger
  have f4: "ll B' A P = ll B' A Q"
    using f1 by (meson \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>col P A B' \<and> col Q A B' \<and> col R A B'\<close> ax_uniqueness)
  then have "incid R (ll B' A Q)"
    using f3 f2 by (metis (no_types) \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness)
  then show ?thesis
    using f4 f1 by (metis \<open>col P A B' \<and> col Q A B' \<and> col R A B'\<close>)
    qed
  qed
  have "col P Q R" if "A = A'" (* very degenerate case, all the 9 points are collinear*)
  proof -
obtain ll :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Lines" where
"\<forall>x0 x1 x2. (\<exists>v3. incid x2 v3 \<and> incid x1 v3 \<and> incid x0 v3) = (incid x2 (ll x0 x1 x2) \<and> incid x1 (ll x0 x1 x2) \<and> incid x0 (ll x0 x1 x2))"
by moura
then have f1: "\<forall>p pa pb. (\<not> col p pa pb \<or> incid p (ll pb pa p) \<and> incid pa (ll pb pa p) \<and> incid pb (ll pb pa p)) \<and> (col p pa pb \<or> (\<forall>l. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid pb l))"
using col_def by auto
then have f2: "incid P (ll B A' P) \<and> incid A' (ll B A' P) \<and> incid B (ll B A' P)"
  by (metis (no_types) \<open>is_a_intersec P A B' A' B\<close> is_a_intersec_def)
have "incid P (ll B' A' P) \<and> incid A' (ll B' A' P) \<and> incid B' (ll B' A' P)"
    using f1 \<open>is_a_intersec P A B' A' B\<close> is_a_intersec_def that by auto
  then have f3: "P = A'"
    using f2 by (metis \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness incidA_lAB incidB_lAB that)
  have f4: "incid R (ll C A' R) \<and> incid A' (ll C A' R) \<and> incid C (ll C A' R)"
    using f1 \<open>is_a_intersec R A C' A' C\<close> is_a_intersec_def by force
  have "incid R (ll C' A' R) \<and> incid A' (ll C' A' R) \<and> incid C' (ll C' A' R)"
    using f1 \<open>is_a_intersec R A C' A' C\<close> is_a_intersec_def that by force
  then have "R = A'"
    using f4 by (metis \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness incidA_lAB incidB_lAB that)
  then show ?thesis
    using f3 f1 by (meson incidA_lAB incidB_lAB)
  qed
  have "col P Q R" if "B = C" (* case where B = C = Q and P,Q,R belong to A'B *)
  proof -
    have "col P A' B \<and> col Q A' B \<and> col R A' B"
    proof -
obtain ll :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Lines" where
f1: "\<forall>p pa pb. (\<not> col p pa pb \<or> incid p (ll pb pa p) \<and> incid pa (ll pb pa p) \<and> incid pb (ll pb pa p)) \<and> (col p pa pb \<or> (\<forall>l. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid pb l))"
using col_def by moura
then have f2: "incid Q (ll C B' Q) \<and> incid B' (ll C B' Q) \<and> incid C (ll C B' Q)"
by (metis (no_types) \<open>is_a_intersec Q B C' B' C\<close> is_a_intersec_def)
have "incid Q (ll C' C Q) \<and> incid C (ll C' C Q) \<and> incid C' (ll C' C Q)"
using f1 \<open>is_a_intersec Q B C' B' C\<close> is_a_intersec_def that by force
  then have "Q = C"
using f2 by (metis (no_types) \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness incidA_lAB incidB_lAB that)
then show ?thesis
using f1 by (metis (no_types) \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec R A C' A' C\<close> is_a_intersec_def that)
    qed
    then show "col P Q R"
    proof -
obtain ll :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Lines" where
"\<forall>x0 x1 x2. (\<exists>v3. incid x2 v3 \<and> incid x1 v3 \<and> incid x0 v3) = (incid x2 (ll x0 x1 x2) \<and> incid x1 (ll x0 x1 x2) \<and> incid x0 (ll x0 x1 x2))"
by moura
then have f1: "\<forall>p pa pb. (\<not> col p pa pb \<or> incid p (ll pb pa p) \<and> incid pa (ll pb pa p) \<and> incid pb (ll pb pa p)) \<and> (col p pa pb \<or> (\<forall>l. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid pb l))"
using col_def by auto
then have f2: "incid Q (ll B A' Q) \<and> incid A' (ll B A' Q) \<and> incid B (ll B A' Q)"
using \<open>col P A' B \<and> col Q A' B \<and> col R A' B\<close> by blast
have f3: "incid R (ll B A' R) \<and> incid A' (ll B A' R) \<and> incid B (ll B A' R)"
  using f1 \<open>col P A' B \<and> col Q A' B \<and> col R A' B\<close> by blast
have f4: "incid P (ll B A' P) \<and> incid A' (ll B A' P) \<and> incid B (ll B A' P)"
    using f1 \<open>col P A' B \<and> col Q A' B \<and> col R A' B\<close> by blast
  have f5: "incid R (ll B A' Q)"
    using f3 f2 by (metis (no_types) \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness)
  have "incid P (ll B A' Q)"
    using f4 f2 by (metis (no_types) \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness)
  then show ?thesis
    using f5 f2 f1 by meson
    qed
  qed
  have "col P Q R" if "B = B'" (* very degenerate case, the 9 points are collinear *)
  proof -
obtain ll :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Lines" where
"\<forall>x0 x1 x2. (\<exists>v3. incid x2 v3 \<and> incid x1 v3 \<and> incid x0 v3) = (incid x2 (ll x0 x1 x2) \<and> incid x1 (ll x0 x1 x2) \<and> incid x0 (ll x0 x1 x2))"
by moura
then have f1: "\<forall>p pa pb. (\<not> col p pa pb \<or> incid p (ll pb pa p) \<and> incid pa (ll pb pa p) \<and> incid pb (ll pb pa p)) \<and> (col p pa pb \<or> (\<forall>l. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid pb l))"
using col_def by auto
then have f2: "incid Q (ll C B' Q) \<and> incid B' (ll C B' Q) \<and> incid C (ll C B' Q)"
by (meson \<open>is_a_intersec Q B C' B' C\<close> is_a_intersec_def)
have "incid Q (ll C' B' Q) \<and> incid B' (ll C' B' Q) \<and> incid C' (ll C' B' Q)"
using f1 \<open>is_a_intersec Q B C' B' C\<close> is_a_intersec_def that by force
  then have f3: "Q = B'"
using f2 by (metis \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness incidA_lAB incidB_lAB that)
have f4: "incid B' (line A' B)"
    using incidB_lAB that by blast
  have f5: "incid P (ll B' A P) \<and> incid A (ll B' A P) \<and> incid B' (ll B' A P)"
    using f1 by (meson \<open>is_a_intersec P A B' A' B\<close> is_a_intersec_def)
  have f6: "incid P (ll B' A' P) \<and> incid A' (ll B' A' P) \<and> incid B' (ll B' A' P)"
    using f1 by (metis (no_types) \<open>is_a_intersec P A B' A' B\<close> is_a_intersec_def that)
  have "B' \<noteq> A'"
    using \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> that by fastforce
  then have "P = B'"
    using f6 f5 f4 by (metis (no_types) \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness incidA_lAB incidB_lAB)
  then show ?thesis
    using f3 f1 by (meson incidA_lAB incidB_lAB)
  qed
  have "col P Q R" if "C = C'" (* again, very degenerate case, the 9 points are collinear *)
  proof -
obtain ll :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Lines" where
"\<forall>x0 x1 x2. (\<exists>v3. incid x2 v3 \<and> incid x1 v3 \<and> incid x0 v3) = (incid x2 (ll x0 x1 x2) \<and> incid x1 (ll x0 x1 x2) \<and> incid x0 (ll x0 x1 x2))"
by moura
then have f1: "\<forall>p pa pb. (\<not> col p pa pb \<or> incid p (ll pb pa p) \<and> incid pa (ll pb pa p) \<and> incid pb (ll pb pa p)) \<and> (col p pa pb \<or> (\<forall>l. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid pb l))"
using col_def by auto
then have f2: "incid Q (ll C' B Q) \<and> incid B (ll C' B Q) \<and> incid C' (ll C' B Q)"
using \<open>is_a_intersec Q B C' B' C\<close> is_a_intersec_def by force
have "incid Q (ll C' B' Q) \<and> incid B' (ll C' B' Q) \<and> incid C' (ll C' B' Q)"
  using f1 \<open>is_a_intersec Q B C' B' C\<close> is_a_intersec_def that by force
then have f3: "Q = C'"
    using f2 by (metis \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness incidA_lAB incidB_lAB that)
  have f4: "incid R (ll C' A R) \<and> incid A (ll C' A R) \<and> incid C' (ll C' A R)"
    using f1 \<open>is_a_intersec R A C' A' C\<close> is_a_intersec_def by force
  have "incid R (ll C' A' R) \<and> incid A' (ll C' A' R) \<and> incid C' (ll C' A' R)"
    using f1 \<open>is_a_intersec R A C' A' C\<close> is_a_intersec_def that by force
  then have "R = C'"
    using f4 by (metis (no_types) \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness incidA_lAB incidB_lAB that)
  then show ?thesis
    using f3 f1 by (meson incidA_lAB incidB_lAB)
  qed
  have "col P Q R" if "A' = B'" (* case where P = A' = B', and P,Q,R belong to A'C *)
  proof -
    have "P = A'"
      by (metis \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec P A B' A' B\<close> ax_uniqueness col_def incidA_lAB incidB_lAB is_a_intersec_def that)
    have "col P A' C \<and> col Q A' C \<and> col R A' C"
      using \<open>P = A'\<close> \<open>is_a_intersec Q B C' B' C\<close> \<open>is_a_intersec R A C' A' C\<close> col_AAB is_a_intersec_def that by auto
    then show "col P Q R"
    proof -
obtain ll :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Lines" where
"\<forall>x0 x1 x2. (\<exists>v3. incid x2 v3 \<and> incid x1 v3 \<and> incid x0 v3) = (incid x2 (ll x0 x1 x2) \<and> incid x1 (ll x0 x1 x2) \<and> incid x0 (ll x0 x1 x2))"
by moura
then have f1: "\<forall>p pa pb. (\<not> col p pa pb \<or> incid p (ll pb pa p) \<and> incid pa (ll pb pa p) \<and> incid pb (ll pb pa p)) \<and> (col p pa pb \<or> (\<forall>l. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid pb l))"
using col_def by auto
then have f2: "incid R (ll C A' R) \<and> incid A' (ll C A' R) \<and> incid C (ll C A' R)"
using \<open>col P A' C \<and> col Q A' C \<and> col R A' C\<close> by blast
have f3: "incid P (ll C A' P) \<and> incid A' (ll C A' P) \<and> incid C (ll C A' P)"
  using f1 \<open>col P A' C \<and> col Q A' C \<and> col R A' C\<close> by blast
have f4: "ll C A' P = ll C A' Q"
    using f1 by (meson \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>col P A' C \<and> col Q A' C \<and> col R A' C\<close> ax_uniqueness)
  then have f5: "incid R (ll C A' Q)"
    using f3 f2 by (metis (no_types) \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness)
  have "incid P (ll C A' Q)"
    using f4 f3 by presburger
  then show ?thesis
    using f5 f1 by (meson \<open>col P A' C \<and> col Q A' C \<and> col R A' C\<close>)
    qed
  qed
  have "col P Q R" if "A' = C'" (* case where R = A' = B', the points P,Q,R belong to A'B *)
  proof -
    have "R = A'"
      by (metis \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec R A C' A' C\<close> ax_uniqueness col_def incidA_lAB incidB_lAB is_a_intersec_def that)
    have "col P A' B \<and> col Q A' B \<and> col R A' B"
      using \<open>R = A'\<close> \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec Q B C' B' C\<close> col_def is_a_intersec_def that by auto
    then show "col P Q R"
    proof -
obtain ll :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Lines" where
"\<forall>x0 x1 x2. (\<exists>v3. incid x2 v3 \<and> incid x1 v3 \<and> incid x0 v3) = (incid x2 (ll x0 x1 x2) \<and> incid x1 (ll x0 x1 x2) \<and> incid x0 (ll x0 x1 x2))"
by moura
then have f1: "\<forall>p pa pb. (\<not> col p pa pb \<or> incid p (ll pb pa p) \<and> incid pa (ll pb pa p) \<and> incid pb (ll pb pa p)) \<and> (col p pa pb \<or> (\<forall>l. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid pb l))"
using col_def by auto
  then have f2: "incid R (ll B A' R) \<and> incid A' (ll B A' R) \<and> incid B (ll B A' R)"
using \<open>col P A' B \<and> col Q A' B \<and> col R A' B\<close> by blast
  have f3: "incid P (ll B A' P) \<and> incid A' (ll B A' P) \<and> incid B (ll B A' P)"
    using f1 \<open>col P A' B \<and> col Q A' B \<and> col R A' B\<close> by blast
  have f4: "ll B A' P = ll B A' Q"
    using f1 by (meson \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>col P A' B \<and> col Q A' B \<and> col R A' B\<close> ax_uniqueness)
  then have "incid R (ll B A' Q)"
    using f3 f2 by (metis (no_types) \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness)
  then show ?thesis
    using f4 f1 by (metis \<open>col P A' B \<and> col Q A' B \<and> col R A' B\<close>)
    qed
  qed
  have "col P Q R" if "B' = C'" (* case where Q = B' = C', the points P,Q,R belong to AB' *)
  proof -
    have "Q = B'"
      by (metis \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec Q B C' B' C\<close> ax_uniqueness col_def incidA_lAB incidB_lAB is_a_intersec_def that)
    have "col P A B' \<and> col Q A B' \<and> col R A B'"
      using \<open>Q = B'\<close> \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec R A C' A' C\<close> col_ABA is_a_intersec_def that by blast
    then show "col P Q R"
    proof -
obtain ll :: "Points \<Rightarrow> Points \<Rightarrow> Points \<Rightarrow> Lines" where
"\<forall>x0 x1 x2. (\<exists>v3. incid x2 v3 \<and> incid x1 v3 \<and> incid x0 v3) = (incid x2 (ll x0 x1 x2) \<and> incid x1 (ll x0 x1 x2) \<and> incid x0 (ll x0 x1 x2))"
  by moura
then have f1: "\<forall>p pa pb. (\<not> col p pa pb \<or> incid p (ll pb pa p) \<and> incid pa (ll pb pa p) \<and> incid pb (ll pb pa p)) \<and> (col p pa pb \<or> (\<forall>l. \<not> incid p l \<or> \<not> incid pa l \<or> \<not> incid pb l))"
    using col_def by auto
  then have f2: "incid R (ll B' A R) \<and> incid A (ll B' A R) \<and> incid B' (ll B' A R)"
    using \<open>col P A B' \<and> col Q A B' \<and> col R A B'\<close> by blast
  have f3: "incid P (ll B' A P) \<and> incid A (ll B' A P) \<and> incid B' (ll B' A P)"
    using f1 \<open>col P A B' \<and> col Q A B' \<and> col R A B'\<close> by blast
  have f4: "ll B' A P = ll B' A Q"
    using f1 by (meson \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>col P A B' \<and> col Q A B' \<and> col R A B'\<close> ax_uniqueness)
  then have "incid R (ll B' A Q)"
    using f3 f2 by (metis (no_types) \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> ax_uniqueness)
  then show ?thesis
    using f4 f1 by (metis (no_types) \<open>col P A B' \<and> col Q A B' \<and> col R A B'\<close>)
    qed
  qed
  have "col P Q R" if "A \<noteq> B \<and> A \<noteq> C \<and> A \<noteq> A' \<and> B \<noteq> C \<and> B \<noteq> B' \<and> C \<noteq> C' \<and> A'\<noteq> B'
\<and> A' \<noteq> C' \<and> B' \<noteq> C'"
  proof -
    have "distinct6 A B C A' B' C'"
      using \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> distinct6_def that by auto
    have "is_a_proper_intersec P A B' A' B"
      using \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec P A B' A' B\<close> is_a_intersec_def is_a_proper_intersec_def by auto
    have "is_a_proper_intersec Q B C' B' C"
      using \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec Q B C' B' C\<close> is_a_intersec_def is_a_proper_intersec_def by auto
    have "is_a_proper_intersec R A C' A' C"
      using \<open>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C\<close> \<open>is_a_intersec R A C' A' C\<close> is_a_intersec_def is_a_proper_intersec_def by auto
    show "col P Q R"
      using \<open>col A B C\<close> \<open>col A' B' C'\<close> \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_proper_intersec P A B' A' B\<close> \<open>is_a_proper_intersec Q B C' B' C\<close> \<open>is_a_proper_intersec R A C' A' C\<close> assms is_pappus1_def by blast sorry
  qed
  show "col P Q R"
    using \<open>A = A' \<Longrightarrow> col P Q R\<close> \<open>A = B \<Longrightarrow> col P Q R\<close> \<open>A = C \<Longrightarrow> col P Q R\<close> \<open>A \<noteq> B \<and> A \<noteq> C \<and> A \<noteq> A' \<and> B \<noteq> C \<and> B \<noteq> B' \<and> C \<noteq> C' \<and> A' \<noteq> B' \<and> A' \<noteq> C' \<and> B' \<noteq> C' \<Longrightarrow> col P Q R\<close> \<open>A' = B' \<Longrightarrow> col P Q R\<close> \<open>A' = C' \<Longrightarrow> col P Q R\<close> \<open>B = B' \<Longrightarrow> col P Q R\<close> \<open>B = C \<Longrightarrow> col P Q R\<close> \<open>B' = C' \<Longrightarrow> col P Q R\<close> \<open>C = C' \<Longrightarrow> col P Q R\<close> by blast
qed
  have "col P Q R" if "distinct6 A B C A' B' C'" and "col A B C" and "col A' B' C'"
and "is_a_intersec P A B' A' B" and "is_a_intersec Q B C' B' C" and "is_a_intersec R A C' A' C"
  proof -
    have "col P Q R" if "line A B' = line A' B"
      using \<open>col A B C\<close> \<open>col A' B' C'\<close> \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec Q B C' B' C\<close> \<open>is_a_intersec R A C' A' C\<close> degenerate_hexagon_is_pappus that by blast
    have "col P Q R" if "line B C' = line B' C"
      using \<open>col A B C\<close> \<open>col A' B' C'\<close> \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec Q B C' B' C\<close> \<open>is_a_intersec R A C' A' C\<close> degenerate_hexagon_is_pappus that by blast
    have "col P Q R" if "line A' C = line A C'"
      using \<open>col A B C\<close> \<open>col A' B' C'\<close> \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_intersec P A B' A' B\<close> \<open>is_a_intersec Q B C' B' C\<close> \<open>is_a_intersec R A C' A' C\<close> degenerate_hexagon_is_pappus that by auto
    have "col P Q R" if "line A B' \<noteq> line A' B" and "line B C' \<noteq> line B' C" and
"line A C' \<noteq> line A' C"
    proof -
      have "is_a_proper_intersec P A B' A' B"
        using \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_intersec P A B' A' B\<close> distinct6_def is_a_intersec_def is_a_proper_intersec_def that(1) by auto
      have "is_a_proper_intersec Q B C' B' C"
        using \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_intersec Q B C' B' C\<close> distinct6_def is_a_intersec_def is_a_proper_intersec_def that(2) by auto
      have "is_a_proper_intersec R A C' A' C"
        using \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_intersec R A C' A' C\<close> distinct6_def is_a_intersec_def is_a_proper_intersec_def that(3) by auto
      show "col P Q R"
        using \<open>col A B C\<close> \<open>col A' B' C'\<close> \<open>distinct6 A B C A' B' C'\<close> \<open>is_a_proper_intersec P A B' A' B\<close> \<open>is_a_proper_intersec Q B C' B' C\<close> \<open>is_a_proper_intersec R A C' A' C\<close> assms is_pappus1_def by blast
    qed
    show "col P Q R"
      using \<open>\<lbrakk>line A B' \<noteq> line A' B; line B C' \<noteq> line B' C; line A C' \<noteq> line A' C\<rbrakk> \<Longrightarrow> col P Q R\<close> \<open>line A B' = line A' B \<Longrightarrow> col P Q R\<close> \<open>line A' C = line A C' \<Longrightarrow> col P Q R\<close> \<open>line B C' = line B' C \<Longrightarrow> col P Q R\<close> by fastforce
  qed
  show "is_pappus2 A B C A' B' C' P Q R"
    using \<open>\<And>R Q P C' C B' B A' A. \<lbrakk>A \<noteq> B' \<and> A' \<noteq> B \<and> line A B' \<noteq> line A' B \<and> B \<noteq> C' \<and> B' \<noteq> C \<and> line B C' \<noteq> line B' C \<and> A \<noteq> C' \<and> A' \<noteq> C \<and> line A C' \<noteq> line A' C; col A B C; col A' B' C'; is_a_intersec P A B' A' B; is_a_intersec Q B C' B' C; is_a_intersec R A C' A' C\<rbrakk> \<Longrightarrow> col P Q R\<close> \<open>\<lbrakk>distinct6 A B C A' B' C'; col A B C; col A' B' C'; is_a_intersec P A B' A' B; is_a_intersec Q B C' B' C; is_a_intersec R A C' A' C\<rbrakk> \<Longrightarrow> col P Q R\<close> is_pappus2_def by blast
qed

lemma pappus_equiv: "is_pappus1 A B C A' B' C' P Q R = is_pappus2 A B C A' B' C' P Q R"
  using pappus12 pappus21 by blast

end
