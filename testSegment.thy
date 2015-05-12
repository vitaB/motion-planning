theory testSegment
imports testPoint
begin
(*http://www.inf.ed.ac.uk/publications/thesis/online/IM080566.pdf*)
typedef segment = "{{A, B} :: pt set |A B. A \<noteq> B}" by(rule collinear_empty)
consts between ::" pt \<Rightarrow> pt \<Rightarrow> pt \<Rightarrow> bool"

definition "same_side E A B \<equiv> E \<noteq> A \<and> E \<noteq> B \<and> collinear {E, A, B} \<and> \<not>between A E B"
definition "endpoints \<equiv> Rep_segment"
definition "inside AB P \<equiv> \<exists>A B. endpoints AB = {A, B} \<and> between A P B"
definition "outside AB P \<equiv> \<exists>A B. endpoints AB = {A, B} \<and> collinear {A, B, P} \<and> \<not>between A P B"
definition "line_meets_segment a AB \<equiv> \<exists> P. inside AB P \<and> on_line P a"
definition "the_segment A B \<equiv> Abs_segment {A, B}"
definition "same_half_plane a A B \<equiv> \<not>on_line A a \<and> \<not>on_line B a 
\<and> (A = B \<or> (\<exists>\<alpha>. line_on_plane a \<alpha> \<and> in_plane A \<alpha> \<and> in_plane B \<alpha>) \<and> \<not>line_meets_segment a (the_segment A B))"

theorem AxiomII1a: "(between A B C) \<Longrightarrow> A\<noteq>B \<and> A\<noteq>C \<and> B\<noteq>C" sorry
theorem AxiomII1b: "between A B C \<Longrightarrow> collinear {A, B, C}" sorry
theorem AxiomII1c: "between C B A \<Longrightarrow> between A B C" sorry
theorem AxiomII2: "A\<noteq>C \<Longrightarrow> \<exists> B. between A C B" sorry
theorem AxiomII3: "between A B C \<Longrightarrow> \<not>between B A C" sorry
theorem AxiomII4: "\<lbrakk> \<not>collinear {A,B,C};
line_on_plane a (plane_of A B C);
\<not>on_line A a; \<not>on_line B a; \<not>on_line C a;
line_meets_segment a (the_segment A B) \<rbrakk>
\<Longrightarrow> (line_meets_segment a (the_segment A C) \<or> line_meets_segment a (the_segment B C))" sorry
theorem the_segment: assumes "A \<noteq> B"
shows "endpoints (the_segment A B) = {A, B}" sorry
theorem segment_symmetry: shows "the_segment A B = the_segment B A" sorry
theorem inside_between: assumes "A \<noteq> B \<and> inside (the_segment A B) P"
shows "between A P B" sorry
theorem between_inside: assumes "between A P B"
shows "inside (the_segment A B) P" sorry
corollary AxiomII4_col:
assumes "\<not> collinear {A, B, C} \<and>
\<not> collinear {A, B, E} \<and> \<not> collinear {C, D, E} \<and> planar {A, B, C, D, E} \<and> between A D B"
shows "\<exists>F. collinear {D, E, F} \<and> (between A F C \<or> between B F C)" sorry
theorem three: assumes "A \<noteq> C" shows "\<exists>D. between A D C" sorry
theorem between_implies_same_side: assumes "between E A B \<or> between E B A" shows "same_side E A B" sorry
theorem same_side_distinct: assumes "same_side E A B" shows "A \<noteq> E \<and> B\<noteq> E" sorry
theorem same_side_collinear: assumes "same_side E A B" shows "collinear {A, B, E}" sorry
theorem point_on_same_side: assumes "E \<noteq> A"
obtains B where "A \<noteq> B \<and> same_side E A B" sorry
theorem same_side_refl [simp]: assumes "A \<noteq> E" shows "same_side E A A" sorry
theorem same_side_sym: assumes "same_side E B A" shows "same_side E A B" sorry
theorem same_side_trans: assumes "same_side E A B \<and> same_side E B C"
shows "same_side E A C" sorry
theorem segment_add: assumes "between A B C \<and> between A P B \<or> between B P C"
shows "between A P C" sorry
theorem segment_add_converse: assumes "between A B C \<and> between A P C"
shows "B = P \<or> between A P B \<or> between B P C" sorry
lemma collinear_same_side: assumes" collinear {A, B, C} \<and> A \<noteq> B"
shows "same_side A B C \<or> same_side B A C" sorry
theorem same_half_plane_refl [simp]: assumes "\<not>on_line A a"
shows "same_half_plane a A A" sorry
theorem same_half_plane_sym: assumes "same_half_plane a B A"
shows" same_half_plane a A B" sorry
theorem same_half_plane_trans: assumes "same_half_plane a A B \<and> same_half_plane a B C"
shows "same_half_plane a A C" sorry
theorem same_side_trichotomy: assumes "collinear {A, B, C, E} \<and> A \<noteq> E \<and> B \<noteq> E \<and> C \<noteq> E"
shows "same_side E A B \<or> same_side E A C \<or> same_side E B C" sorry


typedef ray = "{{P. same_side E A P} |E A. A \<noteq> E}" sorry
definition "on_ray P h \<equiv> P \<in> Rep_ray h"
definition "emanates_from h E \<equiv> \<exists>A. \<forall>P. on_ray P h \<longleftrightarrow> same_side E A P"
definition "start_point h \<equiv> THE E. emanates_from h E"
definition "line_of_ray h \<equiv> THE a. \<forall> P. on_ray P h \<longrightarrow> on_line P a"
definition "the_ray E A \<equiv> THE h. on_ray A h \<and> start_point h = E"
lemma ray_def_lemma: assumes "emanates_from h E \<and> on_ray A h"
shows "\<forall> P . on_ray P h \<longleftrightarrow> sam_side E A P" sorry
lemma rays_are_open_lemma: assumes "emanates_from h E" shows "\<not>on_ray E h" sorry
theorem start_points_are_unique: shows "\<exists>!E. emanates_from h E" sorry
corollary start_point_emanates:
shows "emanates_from h (start_point h)" sorry
theorem rays_are_open [simp]: shows "\<not>on_ray (start_point h) h" sorry
corollary start_point: assumes "on_ray A h"
shows "\<forall> P. on_ray P h \<longleftrightarrow> same_side (start_point h) A P" sorry
theorem ray_on_line: assumes "on_ray P h" shows "on_line P (line_of_ray h)" sorry
theorem start_point_on_line [simp]: shows "on_line (start_point h) (line_of_ray h)" sorry
theorem ray_equality: assumes "\<forall>P. on_ray P h \<longleftrightarrow> on_ray P h'" shows "h = h'" sorry
theorem unique_ray: assumes "A \<noteq> E" shows "\<exists>! h. on_ray A h \<and> start_point h = E" sorry
theorem the_ray: assumes "A \<noteq> E"
shows "on_ray A (the_ray E A) \<and> start_point (the_ray E A) = E" sorry
theorem the_ray2: assumes "on_ray A h" shows "h = the_ray (start_point h) A" sorry
theorem ray_equality2: assumes "same_side E A B" shows "the_ray E A = the_ray E B" sorry
corollary the_ray1 [simp]: assumes "A \<noteq> E" shows "on_ray A (the_ray E A)" sorry
theorem line_of_ray [simp]: assumes "A \<noteq> E"
shows "line_of_ray (the_ray E A) = line_of E A" sorry
corollary collinear_ray: assumes "B \<noteq> C \<and> on_ray A (the_ray B C)" shows "collinear {A, B, C}" sorry
theorem same_side_same_half_plane:
assumes "on_line A a \<and> \<not>on_line B a \<and> same_side A B C" shows "same_half_plane a B C" sorry
theorem rays_form_lines: assumes "h \<noteq> k \<and>
line_of_ray h = line_of_ray k \<and> start_point h = start_point k \<and> on_line P (line_of_ray h)"
shows "P = start_point h \<or> on_ray P h \<or> on_ray P k" sorry

end
