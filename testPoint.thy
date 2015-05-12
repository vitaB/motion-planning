theory testPoint
imports Complex_Main
begin

(*http://www.inf.ed.ac.uk/publications/thesis/online/IM080566.pdf*)

typedecl pt
typedecl line
typedecl plane
consts
on_line ::"pt \<Rightarrow> line \<Rightarrow> bool"
in_plane :: "pt \<Rightarrow> plane \<Rightarrow> bool"

definition "collinear S \<equiv> \<exists> a. \<forall> P\<in>S. on_line P a"
definition "planar S \<equiv> \<exists>\<alpha>. \<forall>P\<in>S. in_plane P \<alpha>"
definition "line_of A B \<equiv> SOME a. on_line A a \<and> on_line B a"
definition "plane_of A B C \<equiv> SOME \<alpha>. in_plane A \<alpha> \<and> in_plane B \<alpha> \<and> in_plane C \<alpha>"
definition "line_on_plane a \<alpha> \<equiv> \<forall> P. on_line P a \<longrightarrow> in_plane P \<alpha>"

theorem AxiomI12 : "A\<noteq>B \<Longrightarrow> \<exists>! a. on_line A a \<and> on_line B a" sorry
theorem AxiomI3a : "\<forall>a. \<exists>A B. A\<noteq>B \<and> on_line A a \<and> on_line B a" sorry
theorem AxiomI3b: "\<exists> A B C. \<not>collinear {A,B,C}" sorry
theorem AxiomI4b: "\<forall> \<alpha>. \<exists> A. in_plane A \<alpha>" sorry
theorem AxiomI45: "\<not>collinear {A,B,C} \<Longrightarrow> \<exists>! \<alpha>. in_plane A \<alpha> \<and> in_plane B \<alpha> \<and> in_plane C \<alpha>" sorry
theorem AxiomI6: "\<lbrakk>A\<noteq>B; in_plane A \<alpha>; in_plane B \<alpha> \<rbrakk> \<Longrightarrow> line_on_plane (line_of A B) \<alpha>" sorry
theorem AxiomI7: "\<lbrakk>\<alpha>\<noteq>\<beta>; in_plane A \<alpha>; in_plane A \<beta> \<rbrakk> \<Longrightarrow> \<exists> B. A\<noteq>B \<and> in_plane B \<alpha> \<and> in_plane B \<beta>" sorry
theorem AxiomI8: "\<exists> A B C D. \<not>planar {A,B,C,D}" sorry
theorem one: assumes "a\<noteq>b \<and> on_line A a \<and> on_line B a \<and> on_line A b \<and> on_line B b"
shows "A = B" sorry
theorem one_rev: assumes "A \<noteq> B \<and> on_line A a \<and> on_line B a"
shows "a = line_of A B" sorry
theorem AxiomI3a_obtain:
obtains A::pt and B::pt where "A \<noteq> B \<and> a = line_of A B" sorry
lemma second_point_on_line: assumes "on_line A a" obtains B where "B \<noteq> A \<and> on_line B a" sorry
lemma second_point: obtains P::pt where "A \<noteq> P" sorry
theorem on_line_of : "on_line A (line_of A B) \<and> on_line B (line_of A B)" sorry
lemma line_of_commutes [simp]: shows "line_of B A = line_of A B" sorry
lemma plane_of_swap [simp]: shows "plane_of A C B = plane_of A B C" sorry
lemma plane_of_rotate [simp]: shows "plane_of B C A = plane_of A B C" sorry
lemma collinear_set_swap [simp]: "shows collinear {A, C, B} = collinear {A, B, C}" sorry
lemma collinear_set_rotate [simp]: shows "collinear {C, A, B} = collinear {A, B, C}" sorry
lemma collinear_empty [simp]: "shows collinear {}" sorry
lemma collinear_pair [simp]: shows "collinear {P, Q}" sorry
lemma collinear_singleton [simp]: shows "collinear {P}" sorry
corollary AxiomI3a_col: assumes "collinear S"
obtains P and Q where "P \<noteq> Q \<and> collinear (S \<union> {P, Q})" sorry
lemma line_of_collinear_points: assumes "collinear S \<and> A \<in> S \<and> B \<in> S \<and> A \<noteq> B"
shows "\<forall> P\<in>S. on_line P (line_of A B)" sorry
theorem collinear_union: assumes "collinear S \<and> collinear T \<and>
A \<in> S \<and> A \<in> T \<and> B \<in> S \<and> B \<in> T \<and> A \<noteq> B" shows "collinear (S \<union> T)" sorry
theorem collinear_subset: assumes "S \<subseteq> T \<and> collinear T" shows "collinear S" sorry
lemma collinear_from_on_line: assumes "on_line A (line_of B C)" shows "collinear {A, B, C}" sorry
lemma on_line_from_collinear:
assumes "collinear {A, B, C} \<and> B \<noteq> C" shows "on_line A (line_of B C)" sorry
theorem construct_triangle: assumes "A \<noteq> B"
obtains C where "\<not>collinear {A, B, C}" sorry
theorem identify_plane_of :
assumes "\<not>collinear {A, B, C} \<and> in_plane A \<alpha> \<and> in_plane B \<alpha> \<and> in_plane C \<alpha>"
shows "\<alpha> = plane_of A B C" sorry
theorem non_collinear_subset: assumes "\<not>collinear S"
obtains A B and C where "{A, B, C} \<subseteq> S \<and> \<not>collinear {A, B, C}" sorry
lemma planar_empty [simp]: shows "planar {}" sorry
lemma plane_of_planar_points: assumes "planar S \<and> A\<in>S \<and> B\<in>S \<and> C\<in>S \<and> \<not>collinear {A, B, C}"
shows "\<forall>P\<in>S. in_plane P (plane_of A B C)" sorry
theorem planar_subset: assumes "S \<subseteq> T \<and> planar T" shows "planar S" sorry
theorem collinear_implies_planar: assumes "collinear S" shows "planar S" sorry
lemma planar_triple [simp]: shows "planar {A, B, C}" sorry
lemma planar_pair [simp]: shows "planar {A, B}" sorry
lemma planar_singleton [simp]: shows "planar {A}" sorry
theorem in_plane_of :
shows "in_plane A (plane_of A B C) \<and> in_plane B (plane_of A B C) \<and> in_plane C (plane_of A B C)" sorry
corollary in_plane_of1 [simp]: shows "in_plane A (plane_of A B C)" sorry
corollary in_plane_of2 [simp]: shows "in_plane B (plane_of A B C)" sorry
corollary in_plane_of3 [simp]: shows "in_plane C (plane_of A B C)" sorry
corollary AxiomI6_col: assumes "collinear S \<and>
A \<in> S \<and> B \<in> S \<and> A \<noteq> B" shows "\<forall>P\<in>S. in_plane P (plane_of A B C)" sorry
theorem planar_union: assumes "planar S \<and> planar T \<and> \<not>collinear (S \<inter> T)"
shows "planar (S \<union> T)" sorry
theorem collinear_union_is_planar:
assumes "collinear S \<and> collinear T \<and> S \<inter> T \<noteq> {}"
shows "planar (S \<union> T)" sorry
theorem plane_of_point_and_line: assumes "\<not>on_line A a"
shows "\<exists>! \<alpha>. in_plane A \<alpha> \<and> line_on_plane a \<alpha>" sorry
corollary AxiomI4b_col: assumes "planar S"
obtains P where "planar (S \<union> {P})" sorry
corollary AxiomI7_col: assumes "planar S \<and> planar T \<and> S \<inter> T \<noteq> {}"
obtains P and Q where "P \<noteq> Q \<and> planar (S \<union> {P, Q}) \<and> planar (T \<union> {P, Q})" sorry
end
