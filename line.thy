theory line
imports point
begin

(*Definition für Segment.*)
definition segment :: "point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment a b \<equiv> \<not> pointsEqual a b"
lemma [simp]: "xCoord A \<noteq> xCoord B \<Longrightarrow> segment A B" by (auto simp add: segment_def)
lemma [simp]: "yCoord A \<noteq> yCoord B \<Longrightarrow> segment A B" by (auto simp add: segment_def)
lemma segment_Sym: "segment a b \<Longrightarrow> segment b a" by(simp add: segment_def)
definition segment_Same :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> segment P R \<Longrightarrow> segment_Same A B P R \<equiv> (pointsEqual A P \<and> pointsEqual B R)"

(*berechnet die yCoordinate für ein bekanntes x für die Gerade AB. Zweipunkteform*)
(*AB darf keine Vertikale sein*)
definition lineFunktionY :: "point2d \<Rightarrow> point2d \<Rightarrow> real \<Rightarrow> real" where
  "xCoord A \<noteq> xCoord B \<Longrightarrow> lineFunktionY A B px \<equiv>
  ((yCoord B - yCoord A)/(xCoord B - xCoord A)) * (px -xCoord A) + yCoord B"

(*Input: Gerade A, Gerade B, Punkt P
Output: Vertikale Strecke mit der xCoordinate P, welche durch yCoord von A und B beschränkt wird*)
definition vertSegment :: "(point2d*point2d) \<Rightarrow> (point2d*point2d) \<Rightarrow> point2d \<Rightarrow> (point2d*point2d)" where
  "xCoord (fst A) \<noteq> xCoord (snd A) \<Longrightarrow> xCoord (fst B) \<noteq> xCoord (snd B) \<Longrightarrow>
  vertSegment A B P \<equiv> (Abs_point2d (xCoord P, lineFunktionY (fst B) (snd B) (xCoord P) ),Abs_point2d (xCoord P, lineFunktionY (fst A) (snd A) (xCoord P) ))"

(*berechne den mittelpunkt der vertikalen Strecke AB*)
definition vertLineMidpoint :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "xCoord A = xCoord B \<Longrightarrow> vertLineMidpoint A B \<equiv> Abs_point2d(xCoord A,(yCoord A + yCoord B)/2)"
lemma verLineMidpointRigth : "segment A B \<Longrightarrow> xCoord A = xCoord B \<Longrightarrow> midpoint (vertLineMidpoint A B) A B"
  by (auto simp add: vertLineMidpoint_def midpoint_def)
  

(*Punkt p befindet sich auf segment AB*)
definition point_on_segment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> collinear p A B \<Longrightarrow> point_on_segment p A B \<equiv> min (xCoord A)(xCoord B) \<le> xCoord p \<and>
  xCoord p \<le> max (xCoord A)(xCoord B) \<and> min (yCoord A)(yCoord B) \<le> yCoord p \<and> yCoord p \<le> max (yCoord A)(yCoord B)"
(*point on segment ist Symmetrisch*)
lemma point_on_segmentSym [simp] : "segment A B \<Longrightarrow> collinear p A B \<Longrightarrow> point_on_segment p A B = point_on_segment p B A"
  apply (subgoal_tac "collinear p B A \<and> segment B A", simp add: point_on_segment_def)
  apply (simp add: max.commute min.commute, simp add: segment_Sym)
done
lemma point_on_segmentSame [simp]: "segment p B \<Longrightarrow> point_on_segment p p B"
  by (simp add: point_on_segment_def segment_Sym)

(*wenn ein Punkt von AB auf einer geraden PR (und ungleich mit Ecken), dann trennt AB die Ecken P und R*)
(****evtl. nicht Beweisbar... für point_on_segment sollte dann eine andere Definition gesucht werden*)
lemma point_on_segment_noRightTurn : "segment P R \<Longrightarrow> A \<noteq> P \<Longrightarrow> A \<noteq> R \<Longrightarrow> collinear A P R \<Longrightarrow>
  point_on_segment A P R \<Longrightarrow> rightTurn A B P \<Longrightarrow> rightTurn A B R \<Longrightarrow> False"
  apply (auto simp add: point_on_segment_def)
sorry
lemma point_on_segment_noRightTurn1 : "segment P R \<Longrightarrow> A \<noteq> P \<Longrightarrow> A \<noteq> R \<Longrightarrow> collinear B P R \<Longrightarrow>
  point_on_segment B P R \<Longrightarrow> rightTurn A B P \<Longrightarrow> rightTurn A B R \<Longrightarrow> False"
  apply (auto simp add: point_on_segment_def)
sorry

(*Strecke A B "trennt" die Punkte P und R, wenn die Endpunkte von P R auf verschiedenen Seiten von AB liegen.*)
definition lineSeparate :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "lineSeparate A B P R \<equiv> (leftTurn A B R  \<and> rightTurn A B P ) \<or> (rightTurn A B R \<and> leftTurn A B P)"
lemma lineSeparateEq : "lineSeparate A B P R = (signedArea A B R * signedArea A B P < 0)"
  apply (simp add: lineSeparate_def)
  apply (metis areaContra2 collSwap colliniearRight conflictingRigthTurns mult_less_0_iff not_less_iff_gr_or_eq rightTurn_def)
done
(*wenn lineSeparate true, dann müssen Strecken segmente sein*)
lemma lineSeparateSegment: "lineSeparate A B P R \<Longrightarrow> segment P R"
  by (simp add: lineSeparate_def segment_def, metis conflictingRigthTurns)
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
  apply (simp , rule iffI, simp add: lineSeparate_def signedArea_def leftTurnDiffPoints)
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
lemma crossingCollinear [dest]: "crossing A B P R \<Longrightarrow> collinear A B P \<Longrightarrow> False"
  apply (simp add: crossing_def)
  by (metis conflictingLeftTurns3 lineSeparate_def notRightTurn1)
lemma crossingRightTurn [dest] : "crossing A B P R \<Longrightarrow> rightTurn A B P \<and> rightTurn A B R \<Longrightarrow> False"
  by (simp add: crossing_def lineSeparate_def, metis conflictingRigthTurns)
lemma crossingLeftTurn [dest] : "crossing A B P R \<Longrightarrow> leftTurn A B P \<and> leftTurn A B R \<Longrightarrow> False"
  by (simp add: crossing_def lineSeparate_def, metis conflictingRigthTurns)

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

(*wenn die Strecken AB und PR sich schneiden, dann können beide Ecken von PR nicht auf der rechten Seite von AB liegen*)
lemma intersectRightTurn: "segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<Longrightarrow>
  rightTurn A B P \<and> rightTurn A B R \<Longrightarrow> False"
  apply (simp only:intersect_def)
by (metis collRotate conflictingRightTurns2 crossingRightTurn notRightTurn point_on_segment_noRightTurn point_on_segment_noRightTurn1)
lemma intersectRightTurn1 : "segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<Longrightarrow>
  rightTurn A R P \<and> rightTurn P B R \<Longrightarrow> False"
  apply (simp only:intersect_def, safe)
  apply (metis crossingRightTurn crossingSym crossingSym1 rightTurnRotate2)
  apply (metis intersectRightTurn intersect_def rightTurnRotate2 segment_Sym)
  apply (metis intersectRightTurn intersect_def rightTurnRotate2 segment_Sym)
  apply (metis notRightTurn rightTurnRotate2)
by (metis notRightTurn)

(*punkt P ist links vom "rechten" Eckpunkt der Strecke AB. D.h. A oder B ist rechts von P*)
definition leftFromSegment ::  "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "segment A B \<Longrightarrow> leftFromSegment A B P \<equiv> leftFromPoint P A \<or> leftFromPoint P B"
(*linke Ecke des Segments*)
definition leftPSegment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "xCoord A \<noteq> xCoord B \<Longrightarrow> leftPSegment A B \<equiv> (if (leftFromPoint A B) then A else B)"
(*rechte Ecke des Segments*)
definition rightPSegment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "xCoord A \<noteq> xCoord B \<Longrightarrow> rightPSegment A B \<equiv> (if (leftFromPoint A B) then B else A)"
lemma legtPNotEqualRightP : "xCoord A \<noteq> xCoord B \<Longrightarrow> leftPSegment A B \<noteq> rightPSegment A B"
  by (auto simp add: rightPSegment_def leftPSegment_def)

definition pointAboveSegment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "segment A B \<Longrightarrow> pointAboveSegment p A B \<equiv> yCoord p > yCoord A \<or> yCoord p > yCoord B"
definition pointBelowSegment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "segment A B \<Longrightarrow> pointBelowSegment p A B \<equiv> yCoord p < yCoord A \<or> yCoord p < yCoord B"

(*Zusätliche Lemmas*)
lemma intersectNotCollinear: "segment a b \<Longrightarrow> segment c d \<Longrightarrow> intersect a b c d \<Longrightarrow>
  \<not>collinear a b c \<Longrightarrow> a \<noteq> c \<and> b \<noteq> c "
  apply (simp add: intersect_def)
by (metis notCollThenDiffPoints)
lemma intersectNotCollinear1: "segment a b \<Longrightarrow> segment c d \<Longrightarrow> intersect a b c d \<Longrightarrow> \<not>collinear d c b \<Longrightarrow> \<not>collinear a c b 
  \<Longrightarrow> rightTurn a d b \<Longrightarrow> rightTurn a c b \<Longrightarrow> False"
  apply (simp add: intersect_def, safe)
  apply (metis crossingLeftTurn notLeftTurn notRightTurn1)
  apply (metis notRightTurn)
by (smt2 intersectRightTurn intersect_def leftRightTurn notRightTurn notRightTurn1 segment_Sym)


(*Lemmas und Definitionen, die momentan nicht gebraucht werden*)
(*(*http://afp.sourceforge.net/browser_info/current/AFP/Impossible_Geometry/Impossible_Geometry.html*)
definition is_intersection_def:
  "is_intersection M A B C D = (collinear A M B \<and> collinear C M D)"
lemma "segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<Longrightarrow> \<exists> M. is_intersection M A B P R"
  apply (simp add: is_intersection_def intersect_def, safe)
  apply (simp add: crossing_def lineSeparate_def, safe)
sorry*)

end
