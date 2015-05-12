theory testAngle
imports testSegment
begin
(*http://www.inf.ed.ac.uk/publications/thesis/online/IM080566.pdf*)
typedef angle = "{{h,k} |h k. line_of_ray h \<noteq> line_of_ray k \<and> start_point h = start_point k}" by(rule collinear_empty)
definition "sides hk \<equiv> Rep_angle hk"
definition "vertex hk \<equiv> THE P. \<forall>h \<in> sides hk. start_point h = P"
definition "rays_form_an_angle h k \<equiv> line_of_ray h \<noteq> line_of_ray k \<and> start_point h = start_point k"
definition "opposite_side hk h \<equiv> THE k. sides hk = {h, k}"
definition plane_of :: "angle \<Rightarrow> plane" where
"plane_of hk \<equiv> THE \<alpha>. \<forall>h \<in> sides hk. \<forall>P. on_ray P h \<longrightarrow> in_plane P \<alpha>"
definition "interior hk P \<equiv> \<exists>h k. sides hk = {h, k}
\<and> (\<forall> Q. on_ray Q h \<longrightarrow> same_half_plane (line_of_ray k) P Q)
\<and> (\<forall> Q. on_ray Q k \<longrightarrow> same_half_plane (line_of_ray h) P Q)"
definition "exterior hk P \<equiv> in_plane P (plane_of hk) \<and> \<not>interior hk P"
definition "supplementary hk hk' \<equiv> hk \<noteq> hk' \<and> (\<exists> h. h \<in> sides hk \<and> h \<in> sides hk'
\<and> line_of_ray (opposite_side hk h) = line_of_ray (opposite_side hk' h))"
definition "the_angle A B C \<equiv> THE hk. sides hk = {the_ray B A, the_ray B C}"
definition "with_sides h k \<equiv> THE hk. sides hk = {h, k}"
theorem angle_vertex:
shows "\<forall> h \<in> sides hk. start_point h = (vertex hk)" by(rule collinear_empty)
theorem sides:
assumes "rays_form_an_angle h k" shows "sides (with_sides h k) = {h, k}" sorry
theorem non_collinear_points_form_an_angle: assumes "\<not>collinear {A, B, C}"
shows "rays_form_an_angle (the_ray A B) (the_ray A C)" sorry
theorem sides2: assumes "\<not>collinear {A, B, C}"
shows "sides (with_sides (the_ray A B) (the_ray A C)) = {the_ray A B, the_ray A C}" sorry
theorem the_angle_with_sides: shows "the_angle A B C = with_sides (the_ray B A) (the_ray B C)" sorry
theorem angle_equality: assumes "the_ray B A = the_ray B A' \<and> the_ray B C = the_ray B C'"
shows "the_angle A B C = the_angle A' B C'" sorry
theorem angle_sym [simp]: shows "the_angle C B A = the_angle A B C" sorry 
theorem interior_side: assumes "sides Ang = {h, k} \<and> on_ray A k"
shows "\<forall> P. interior Ang P \<longrightarrow> same_half_plane (line_of_ray h) A P" sorry
consts congruent_segments :: "segment \<Rightarrow> segment \<Rightarrow> bool"
consts congruent_angles ::" angle \<Rightarrow> angle \<Rightarrow> bool"
definition the_triangle :: "pt \<Rightarrow> pt \<Rightarrow> pt \<Rightarrow> pt set" where
"the_triangle A B C \<equiv> {A,B,C}"
definition congruent_triangles :: "pt set \<Rightarrow> pt set \<Rightarrow> bool" where
"congruent_triangles T1 T2 \<equiv> \<exists>A B C A' B' C'.
T1 = {A, B, C} \<and> T2 = {A', B', C'}
\<and> \<not>collinear T1 \<and> \<not>collinear T2
\<and> congruent_segments (the_segment A B) (the_segment A' B') \<and> congruent_segments (the_segment B C) (the_segment B' C') \<and> congruent_segments (the_segment A C) (the_segment A' C') \<and> congruent_angles (the_angle A B C) (the_angle A' B' C')
\<and> congruent_angles (the_angle B A C) (the_angle B' A' C') \<and> congruent_angles (the_angle A C B) (the_angle A' C' B')"

theorem AxiomIII1: "A \<noteq> C \<Longrightarrow> \<exists> B. same_side A B C \<and> congruent_segments S (the_segment A B)" sorry
theorem AxiomIII2: "\<lbrakk> congruent_segments S T;congruent_segments S' T\<rbrakk> \<Longrightarrow> congruent_segments S S'" sorry
theorem AxiomIII3: "\<lbrakk> between A B C; between A' B' C';
congruent_segments (the_segment A B) (the_segment A' B');
congruent_segments (the_segment B C) (the_segment B' C') \<rbrakk> \<Longrightarrow> cong_segs (the_segment A C) (the_segment A' C')" sorry
theorem AxiomIII4a: "\<not>on_line A (line_of_ray h) \<Longrightarrow> \<exists>! k. rays_form_an_angle h k \<and> congruent_angles h'k' (with_sides h k)
\<and> (\<forall> P. interior (with_sides h k) P \<longrightarrow> same_half_plane (line_of_ray h) A P)" sorry
theorem AxiomIII4b [simp]: "congruent_angles hk hk" sorry
theorem AxiomIII5: "\<lbrakk> \<not>collinear{A, B, C}; \<not>collinear{A', B', C'} ; congruent_segments (the_segment A B) (the_segment A' B') ; congruent_segments (the_segment A C) (the_segment A' C') ; congruent_angles (the_angle B A C) (the_angle B' A' C')
\<rbrakk> \<Longrightarrow> congruent_angles (the_angle A B C) (the_angle A' B' C')" sorry
theorem congruent_segment_refl [simp]: shows "congruent_segments S S" sorry
theorem congruent_segment_sym: assumes "congruent_segments S T" shows "congruent_segments T S" sorry
theorem congruent_segment_trans: assumes "congruent_segments S T \<and> congruent_segments T U"
shows "congruent_segments S U" sorry 
lemma unique_segment_opposite_angle: assumes "\<not>collinear {A, B, C} \<and> same_side B C C' \<and>
congruent_angles S (the_angle B A C) \<and> congruent_angles S (the_angle B A C')"
shows "C = C'" sorry
theorem segment_uniqueness: assumes "A \<noteq> C"
shows "\<exists>! B. same_side A B C \<and> congruent_segments S (the_segment A B)" sorry
theorem twelve: assumes "\<not>collinear {A, B, C} \<and>
\<not>collinear {A', B', C'} \<and>
congruent_segments (the_segment A B) (the_segment A' B') \<and> congruent_segments (the_segment A C) (the_segment A' C')
\<and> congruent_angles (the_angle B A C) (the_angle B' A' C')"
shows "congruent_triangles (the_triangle A B C) (the_triangle A' B' C')" sorry

end
