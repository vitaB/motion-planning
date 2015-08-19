theory segment
imports point
begin

(*Definition for Segment*)
definition segment :: "point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment a b \<equiv> \<not> pointsEqual a b"
lemma [simp]: "xCoord A \<noteq> xCoord B \<Longrightarrow> segment A B" by (auto simp add: segment_def)
lemma [simp]: "yCoord A \<noteq> yCoord B \<Longrightarrow> segment A B" by (auto simp add: segment_def)
lemma [simp]: "leftFromPoint A B \<Longrightarrow> segment A B" by (simp add: leftFromPoint_def)
lemma segment_Sym: "segment a b \<Longrightarrow> segment b a" by(simp add: segment_def)
definition segment_Same :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> segment P R \<Longrightarrow> segment_Same A B P R \<equiv> (pointsEqual A P \<and> pointsEqual B R)"

(*left corner of the segment*)
definition leftPSegment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "xCoord A \<noteq> xCoord B \<Longrightarrow> leftPSegment A B \<equiv> (if (leftFromPoint A B) then A else B)"
(*right corner of the segment*)
definition rightPSegment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "xCoord A \<noteq> xCoord B \<Longrightarrow> rightPSegment A B \<equiv> (if (leftFromPoint A B) then B else A)"
lemma leftPNotEqualRightP : "xCoord A \<noteq> xCoord B \<Longrightarrow> leftPSegment A B \<noteq> rightPSegment A B"
  by (auto simp add: rightPSegment_def leftPSegment_def)
lemma leftPRightPSimp [simp] : "xCoord p \<noteq> xCoord q \<Longrightarrow> p = leftPSegment p q \<Longrightarrow>
  q = rightPSegment p q"
  by (auto simp add: leftPSegment_def rightPSegment_def)
lemma leftPRightPSimp1 [simp] : "xCoord p \<noteq> xCoord q \<Longrightarrow> q = rightPSegment p q \<Longrightarrow>
  p = leftPSegment p q"
  by (auto simp add: leftPSegment_def rightPSegment_def)


(*Point p is on segment AB*)
definition point_on_segment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "segment A B \<Longrightarrow> collinear p A B \<Longrightarrow> point_on_segment p A B \<equiv>
  min (xCoord A)(xCoord B) \<le> xCoord p \<and> xCoord p \<le> max (xCoord A)(xCoord B) \<and>
  min (yCoord A)(yCoord B) \<le> yCoord p \<and> yCoord p \<le> max (yCoord A)(yCoord B)"
(*point_on_segment is symmetrical*)
lemma point_on_segmentSym: "segment A B \<Longrightarrow> collinear p A B \<Longrightarrow>
  point_on_segment p A B = point_on_segment p B A"
  apply (subgoal_tac "collinear p B A \<and> segment B A", simp add: point_on_segment_def)
by (simp add: max.commute min.commute, simp add: segment_Sym)
lemma point_on_segmentSame [simp]: "segment p B \<Longrightarrow> point_on_segment p p B"
  by (simp add: point_on_segment_def segment_Sym)

(*wenn ein Punkt von AB auf einer geraden PR (und ungleich mit Ecken), dann trennt AB die Ecken P und R*)
(****evtl. nicht Beweisbar... für point_on_segment sollte dann eine andere Definition gesucht werden*)
lemma point_on_segment_noRightTurn : "segment P R \<Longrightarrow> A \<noteq> P \<Longrightarrow> A \<noteq> R \<Longrightarrow> collinear A P R \<Longrightarrow>
  point_on_segment A P R \<Longrightarrow> rightTurn A B P \<Longrightarrow> rightTurn A B R \<Longrightarrow> False"
  apply (auto simp add: point_on_segment_def)
  apply (case_tac "min (xCoord P) (xCoord R) = xCoord P", simp)
  apply (case_tac "max (xCoord P) (xCoord R) = xCoord P", simp)
  apply (case_tac "max (yCoord P) (yCoord R) = yCoord P", simp)
  apply (case_tac "min (yCoord P) (yCoord R) = yCoord P", simp)
  apply (metis Rep_point2d_inverse prod.collapse xCoord_def yCoord_def)
  apply (subgoal_tac "min (yCoord P) (yCoord R) = yCoord R", simp)
sorry
lemma point_on_segment_noRightTurn1 : "segment P R \<Longrightarrow> A \<noteq> P \<Longrightarrow> A \<noteq> R \<Longrightarrow> collinear B P R \<Longrightarrow>
  point_on_segment B P R \<Longrightarrow> rightTurn A B P \<Longrightarrow> rightTurn A B R \<Longrightarrow> False"
  apply (auto simp add: point_on_segment_def)
sorry

(*Segment AB separates the points P and R when the endpoints of PR lie's on different sides of AB.*)
definition lineSeparate :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "lineSeparate A B P R \<equiv> (leftTurn A B R  \<and> rightTurn A B P )\<or>(rightTurn A B R \<and> leftTurn A B P)"
lemma lineSeparateEq : "lineSeparate A B P R = (signedArea A B R * signedArea A B P < 0)"
  apply (simp add: lineSeparate_def colliniearRight, simp only: rightTurnEq)
by (metis colliniearRight leftTurn_def mult_less_0_iff notLeftTurn not_less_iff_gr_or_eq)
(*wenn lineSeparate true, dann müssen Strecken segmente sein*)
lemma lineSeparateSegment: "lineSeparate A B P R \<Longrightarrow> segment P R"
  by (simp add: lineSeparate_def segment_def, metis conflictingRigthTurns)
lemma lineSeparateSegment1: "lineSeparate A B P R \<Longrightarrow> segment A B"
  apply (simp add: lineSeparate_def segment_def rightTurn_def)
by (metis areaDoublePoint less_numeral_extra(3))
(*additional Lemmas*)
lemma lineSeparateSame1 [simp]:"\<not>lineSeparate A B A B" by (simp add: lineSeparate_def)
lemma lineSeparateSame2 [simp]:"\<not>lineSeparate A B B A" by (simp add: lineSeparate_def)
(*lineSeparate is symmetrical*)
lemma lineSeparateSym: "lineSeparate A B P R = lineSeparate B A P R"
  by (auto simp add: lineSeparate_def signedArea_def leftTurn_def rightTurn_def)
lemma lineSeparateSym1: "lineSeparate A B P R = lineSeparate A B R P"
 by (auto simp add: lineSeparate_def leftTurn_def)

(*(real)intersection between AB and PR Segment Segment*)
definition crossing ::  "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "crossing A B P R \<equiv> (lineSeparate A B P R \<and> lineSeparate P R A B)"
lemma crossingSegment [simp]:"crossing A B P R \<Longrightarrow> segment A B" 
  apply (simp add: crossing_def segment_def lineSeparate_def rightTurn_def)
by (metis areaDoublePoint less_irrefl)
lemma crossingSegment1 [simp]:"crossing A B P R \<Longrightarrow> segment P R"
  apply (simp add: crossing_def segment_def lineSeparate_def rightTurn_def)
by (metis areaDoublePoint2 less_numeral_extra(3))
(*crossing is symmetrical*)
lemma crossingSym: "crossing A B P R = crossing B A P R"
  by (auto simp add: crossing_def lineSeparate_def)
lemma crossingSym1: "crossing A B P R = crossing P R A B "
  by (auto simp add: crossing_def lineSeparate_def)
(*lemmas with crossing and collinear/leftTurn/rightTurn*)
lemma crossingCollinear [dest]: "crossing A B P R \<Longrightarrow> collinear A B P \<Longrightarrow> False"
  by (simp add: crossing_def, metis conflictingLeftTurns3 lineSeparate_def notRightTurn1)
lemma crossingRightTurn [dest] : "crossing A B P R \<Longrightarrow> rightTurn A B P \<and> rightTurn A B R \<Longrightarrow> False"
  by (simp add: crossing_def lineSeparate_def, metis conflictingRigthTurns)
lemma crossingLeftTurn [dest] : "crossing A B P R \<Longrightarrow> leftTurn A B P \<and> leftTurn A B R \<Longrightarrow> False"
  by (simp add: crossing_def lineSeparate_def, metis conflictingRigthTurns)

(*intersection, even if endpoint is on segment*)
definition intersect :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<equiv> (crossing A B P R \<or>
  (collinear A B P \<and> point_on_segment P A B) \<or> (collinear A B R \<and> point_on_segment R A B)
  \<or> (collinear P R A \<and> point_on_segment A P R) \<or> (collinear P R B \<and> point_on_segment B P R))"
lemma intersectSame [simp] : "segment A B \<Longrightarrow> intersect A B A B" by (simp add: intersect_def)
lemma crossingIntersect [simp]: "crossing A B P R \<Longrightarrow> intersect A B P R"
  apply (subgoal_tac "segment A B \<and> segment P R")
by (auto simp add: intersect_def crossingSym1, simp only: crossingSegment1)
lemma intersectSym : "intersect A B P R = intersect B A P R" sorry
lemma intersectSym1 : "intersect A B P R = intersect P R A B" sorry

(*if the segments AB and PR intersect, then both corners of PR can not be on the same side of AB*)
lemma intersectRightTurn: "segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<Longrightarrow>
  rightTurn A B P \<and> rightTurn A B R \<Longrightarrow> False"
  apply (simp only: intersect_def, auto)
  apply (metis conflictingRigthTurns1 point_on_segment_noRightTurn rightTurnRotate)
by (metis leftRightTurn point_on_segment_noRightTurn1 rightTurnEq)
lemma intersectRightTurn1 : "segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<Longrightarrow>
  rightTurn A R P \<and> rightTurn P B R \<Longrightarrow> False"
  apply (simp only:intersect_def, safe)
  apply (metis crossingRightTurn crossingSym crossingSym1 rightTurnRotate2)
  apply (metis intersectRightTurn intersect_def rightTurnRotate2 segment_Sym)
  apply (metis intersectRightTurn intersect_def rightTurnRotate2 segment_Sym)
  apply (metis notRightTurn rightTurnRotate2)
by (metis notRightTurn)

(*additional Lemmas for intersect*)
lemma intersectNotCollinear: "segment a b \<Longrightarrow> segment c d \<Longrightarrow> intersect a b c d \<Longrightarrow>
  \<not>collinear a b c \<Longrightarrow> a \<noteq> c \<and> b \<noteq> c "
  by (simp add: intersect_def, metis notCollThenDiffPoints)
lemma intersectNotCollinear1: "segment a b \<Longrightarrow> segment c d \<Longrightarrow> intersect a b c d \<Longrightarrow>
  \<not>collinear d c b \<Longrightarrow> \<not>collinear a c b  \<Longrightarrow> rightTurn a d b \<Longrightarrow> rightTurn a c b \<Longrightarrow> False"
  apply (simp add: intersect_def, safe)
  apply (metis crossingLeftTurn notLeftTurn notRightTurn1, metis notRightTurn)
by (smt intersectRightTurn intersect_def leftRightTurn notRightTurn notRightTurn1 segment_Sym)




(*alte Definition*)
(*Lemmas und Definitionen, die momentan nicht gebraucht werden*)
(*(*http://afp.sourceforge.net/browser_info/current/AFP/Impossible_Geometry/Impossible_Geometry.html*)
definition is_intersection_def:
  "is_intersection M A B C D = (collinear A M B \<and> collinear C M D)"
lemma "segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<Longrightarrow> \<exists> M. is_intersection M A B P R"
  apply (simp add: is_intersection_def intersect_def, safe)
  apply (simp add: crossing_def lineSeparate_def, safe)
sorry*)

end
