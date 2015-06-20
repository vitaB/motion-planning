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
  
(*Punkt befindet sich auf segment*)
definition point_on_segment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> collinear p A B \<Longrightarrow> point_on_segment p A B \<equiv> min (xCoord A)(xCoord B) \<le> xCoord p \<and>
xCoord p \<le> max (xCoord A)(xCoord B) \<and> min (yCoord A)(yCoord B) \<le> yCoord p
\<and> yCoord p \<le> max (yCoord A)(yCoord B)"
(*point on segment ist Symmetrisch*)
lemma point_on_segmentSym [simp] : "segment A B \<Longrightarrow> collinear p A B \<Longrightarrow>
  point_on_segment p A B = point_on_segment p B A"
  apply (subgoal_tac "collinear p B A \<and> segment B A")
  apply (simp add: point_on_segment_def)
  apply (simp add: max.commute min.commute, simp add: segment_Sym)
done
lemma point_on_segmentSame [simp]: "segment p B \<Longrightarrow> point_on_segment p p B"
  by (simp add: point_on_segment_def segment_Sym)

(*Strecke A B "trennt" die Punkte P und R: die Endpunkte von P R liegen auf verschiedenen Seiten von AB.*)
definition lineSeparate :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "lineSeparate A B P R \<equiv> (leftTurn A B R  \<and> rightTurn A B P ) \<or> (rightTurn A B R \<and> leftTurn A B P)"
lemma lineSeparateEq : "lineSeparate A B P R = (signedArea A B R * signedArea A B P < 0)"
  by (simp add: lineSeparate_def, metis mult_less_0_iff leftTurn_def leftRightTurn rightTurn_def)
(*wenn lineSeparate true, dann müssen Strecken segmente sein*)
lemma lineSeparateSegment: "lineSeparate A B P R \<Longrightarrow> segment P R"
  by(simp add: lineSeparate_def segment_def, metis not_less_iff_gr_or_eq leftTurn_def rightTurn_def leftRightTurn)
lemma lineSeparateSegment1: "lineSeparate A B P R \<Longrightarrow> segment A B"
  by (simp add: lineSeparate_def segment_def rightTurn_def, metis areaDoublePoint less_numeral_extra(3))
(*Zusätzliche Lemmas*)
lemma [simp]:"\<not> lineSeparate A B A B" by (simp add: lineSeparate_def)
lemma [simp]:"\<not> lineSeparate A B B A" by (simp add: lineSeparate_def)
lemma [simp]:"\<not> lineSeparate B A A B" by (simp add: lineSeparate_def)
(*line Separate ist symmetrisch*)
lemma lineSeparateSym [simp]: "lineSeparate A B P R = lineSeparate B A P R"
  by (auto simp add: lineSeparate_def signedArea_def leftTurn_def rightTurn_def)

lemma lineSeparateSym1[simp]: "lineSeparate A B P R = lineSeparate A B R P"
 by (auto simp add: lineSeparate_def leftTurn_def)
(*lemma lineSeparateSym2 : "\<not>(lineSeparate A B P R \<longleftrightarrow> lineSeparate P R A B)"
  apply (simp , rule iffI)
  apply (simp add: lineSeparate_def signedArea_def leftTurnDiffPoints)
  apply (safe)
oops*)

(*(echter)Schnitt zwischen Segment A B und Segment P R*)
definition crossing ::  "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "crossing A B P R \<equiv> (lineSeparate A B P R \<and> lineSeparate P R A B)"
lemma crossingSegment [simp]:"crossing A B P R \<Longrightarrow> segment A B" 
  by (simp add: crossing_def segment_def lineSeparate_def rightTurn_def, metis areaDoublePoint less_irrefl)
lemma crossingSegment1 [simp]:"crossing A B P R \<Longrightarrow> segment P R"
  by (simp add: crossing_def segment_def lineSeparate_def rightTurn_def, metis areaDoublePoint2 less_numeral_extra(3))
lemma crossingSym [simp]: "crossing A B P R = crossing B A P R "
  by (auto simp add: crossing_def lineSeparate_def)
lemma crossingSym1 [simp]: "crossing A B P R = crossing P R A B "
  by (auto simp add: crossing_def lineSeparate_def)

(*Schnitt, auch wenn Endpunkt auf Strecke liegt*)
definition intersect :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<equiv>
  (crossing A B P R \<or> (collinear A B P \<and> point_on_segment P A B) \<or> (collinear A B R \<and> point_on_segment R A B)
  \<or> (collinear P R A \<and> point_on_segment A P R) \<or> (collinear P R B \<and> point_on_segment B P R))"
lemma intersectSame [simp] : "segment A B \<Longrightarrow> intersect A B A B" by (simp add: intersect_def)
lemma crossingIntersect [simp]: "crossing A B P R \<Longrightarrow> intersect A B P R"
  apply (subgoal_tac "segment A B \<and> segment P R")
  apply (auto simp add: intersect_def, simp only: crossingSegment1)
done
lemma intersectSym : "intersect A B P R = intersect B A P R" sorry
lemma intersectSym1 : "intersect A B P R = intersect P R A B" sorry

end
