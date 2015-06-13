theory line
imports point
begin

(*Definition für Segment.*)
(*Evtl. wäre ein eigener Datentyp besser*)
definition segment :: "point2d \<Rightarrow> point2d  \<Rightarrow> bool" where
"segment a b \<equiv> \<not> pointsEqual a b"
(*dieses lemma nicht zu simp hinzufügen!*)
lemma segment_Sym: "segment a b \<Longrightarrow> segment b a" by(simp add: segment_def)

definition segment_Same :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> segment P R \<Longrightarrow> segment_Same A B P R \<equiv> (pointsEqual A P \<and> pointsEqual B R)"

definition point_on_segment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> point_on_segment p A B \<equiv>  min (xCoord A)(xCoord B) \<le> xCoord p \<and>
xCoord p \<le> max (xCoord A)(xCoord B) \<and> min (yCoord A)(yCoord B) \<le> yCoord p
\<and> yCoord p \<le> max (yCoord A)(yCoord B)"

(* zwischenPunkt p von segment A B liegt auf A B*)
lemma segment_betwpoint : "segment A B \<Longrightarrow> betwpoint p A B \<longrightarrow> point_on_segment p A B"
  apply (rule impI)
  apply (simp add: betwpoint_def point_on_segment_def)
  apply (erule_tac x = 2 in allE)
  apply (simp)
  apply (auto)
done
(*lemma segment_betwpoint : "segment A B \<Longrightarrow> betwpoint p A B \<longleftrightarrow> point_on_segment p A B \<or> p = A \<or> p = B"
  apply (rule iffI, simp add: segment_betwpoint)
  apply (auto simp add: point_on_segment_def betwpoint_def)
oops*)

(*Strecke A B "trennt" die Punkte P und R*)
definition lineSeparate :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "lineSeparate A B P R \<equiv> (signedArea A B R > 0 \<and> signedArea A B P < 0) \<or> (signedArea A B R < 0 \<and> signedArea A B P > 0)"
lemma lineSeparateSegment: "lineSeparate A B P R \<Longrightarrow> segment P R"
  by(simp add: lineSeparate_def segment_def, metis not_less_iff_gr_or_eq)
lemma lineSeparateSegment1: "lineSeparate A B P R \<Longrightarrow> segment A B"
  by (simp add: lineSeparate_def segment_def, metis areaDoublePoint less_numeral_extra(3))
lemma [simp]:"\<not> lineSeparate A B A B" by (simp add: lineSeparate_def)
lemma [simp]:"\<not> lineSeparate A B B A" by (simp add: lineSeparate_def)
lemma [simp]:"\<not> lineSeparate B A A B" by (simp add: lineSeparate_def)
lemma lineSeparateSym: "lineSeparate A B P R \<longleftrightarrow> lineSeparate B A P R"
  apply (simp add: lineSeparate_def signedArea_def)
  apply (metis less_diff_eq monoid_add_class.add.left_neutral mult.commute)
done
lemma lineSeparateSym1: "lineSeparate A B P R \<longleftrightarrow> lineSeparate A B R P"
 by (auto simp add: lineSeparate_def)
(*lemma lineSeparateSym2 : "\<not>(lineSeparate A B P R \<longleftrightarrow> lineSeparate P R A B)"
  apply (simp , rule iffI)
  apply (simp add: lineSeparate_def signedArea_def leftTurnDiffPoints)
  apply (safe)
oops*)

(*(echter)Schnitt zwischen Segment A B und Segment P R*)
definition crossing ::  "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"crossing A B P R \<equiv>
  let a = signedArea P R A in
  let b = signedArea P R B in
  let c = signedArea A B P in
  let d = signedArea A B R in
   ((a > 0 \<and> b < 0) \<or> (a < 0 \<and> b > 0)) \<and> ((c > 0 \<and> d < 0) \<or> (c < 0 \<and> d > 0))"
lemma crossingSegment [simp] :"crossing A B P R \<Longrightarrow> segment A B" 
  by (simp add: crossing_def segment_def, metis areaDoublePoint less_irrefl)
lemma crossingSegment1 [simp] :"crossing A B P R \<Longrightarrow> segment P R"
   by (simp add: crossing_def segment_def, metis areaDoublePoint2 less_numeral_extra(3))

(*Schnitt, auch wenn Endpunkt auf Strecke liegt*)
definition intersect :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<equiv>
  let a = signedArea P R A in
  let b = signedArea P R B in
  let c = signedArea A B P in
  let d = signedArea A B R in
   ((a > 0 \<and> b < 0) \<or> (a < 0 \<and> b > 0)) \<and> ((c > 0 \<and> d < 0) \<or> (c < 0 \<and> d > 0))
   \<or> (a = 0 \<or> point_on_segment A P R)
   \<or> (b = 0 \<or> point_on_segment B P R)
   \<or> (c = 0 \<or> point_on_segment P A B)
   \<or> (d = 0 \<or> point_on_segment R A B)"

lemma intersectSym : "intersect A B P R \<longleftrightarrow> intersect B A P R" sorry
lemma intersectSym1 : "intersect A B P R \<longleftrightarrow> intersect P R A B" sorry

end
