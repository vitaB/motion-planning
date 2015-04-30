theory line
imports point
begin

record line = 
  sLine :: point2d
  eLine :: point2d
(*line equal*)
(*Punkt links von line*)
(*intersection (line a, line b) echtes Schneiden, unechtes Schneiden*)


(*Polygon, liste/sequenz mit Punkten wo Anfangspunkt und Endpunk gleich sind*)
definition polygon = "line"
(*Punkt inside Polygon*)
(*intersection(Polygon, Line)*)
(*intersection(Polygon, Polygon)*)
(*move Polygon*)

definition convexPolygon = "polygon"
(*wann ist ein polygon convex*)
(*intersection(Polygon, Polygon)*)

(*Intrduce new type without definition*)
typedecl pt
typedecl line
typedecl plane

consts on_line :: "pt \<Rightarrow> line \<Rightarrow> bool"
consts in_plane :: "pt \<Rightarrow> plane \<Rightarrow> bool"

constdefs
  collinear S \<equiv> \<exists> a. \<forall> P\<in>S. on-line P a
  planar S \<equiv> \<exists>\<alpha>. \<forall>P\<in>S. in-plane P \<alpha>
  line-of A B \<equiv> SOME a. on-line A a \<and> on-line B a
  plane-of A B C \<equiv> SOME \<alpha>. in-plane A \<alpha> \<and> in-plane B \<alpha> \<and> in-plane C \<alpha> line-on-plane a \<alpha> \<equiv> \<forall> P. on-line P a −\<rightarrow> in-plane P \<alpha>
axioms
  AxiomI12: A̸=B =\<Rightarrow> \<exists> !a. on-line A a \<and> on-line B a AxiomI3a: \<forall>a. \<exists>A B. A̸=B \<and> on-line A a \<and> on-line B a AxiomI3b: \<exists> A B C. \<not>collinear {A,B,C}
  AxiomI4b:\<forall> \<alpha>. \<exists> A. in-plane A \<alpha>
  AxiomI45: \<not>collinear {A,B,C} =\<Rightarrow> \<exists> !\<alpha>. in-plane A \<alpha> \<and> in-plane B \<alpha> \<and> in-plane C \<alpha> AxiomI6: [ A̸=B; in-plane A \<alpha>; in-plane B \<alpha> ] =\<Rightarrow> line-on-plane (line-of A B) \<alpha>
  AxiomI7: [ \<alpha≯=\<beta>; in-plane A \<alpha>; in-plane A \<beta> ] =\<Rightarrow> \<exists> B. A̸=B \<and> in-plane B \<alpha> \<and> in-plane B \<beta> AxiomI8: \<exists> A B C D. \<not>planar {A,B,C,D}

pt \<equiv> UNIV :: hypvec set
line \<equiv> UNIV :: (pt * pt) set

end
