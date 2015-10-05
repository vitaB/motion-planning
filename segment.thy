theory segment
imports point
begin

(*Definition for Segment*)
definition segment :: "point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment a b \<equiv> \<not> pointsEqual a b"
lemma [simp]: "xCoord A \<noteq> xCoord B \<Longrightarrow> segment A B" by (auto simp add: segment_def)
lemma [simp]: "yCoord A \<noteq> yCoord B \<Longrightarrow> segment A B" by (auto simp add: segment_def)
lemma [simp]: "leftFrom A B \<Longrightarrow> segment A B" by (simp add: leftFrom_def)
lemma segment_Sym: "segment a b \<Longrightarrow> segment b a" by(simp add: segment_def)
definition segment_Same :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> segment P R \<Longrightarrow> segment_Same A B P R \<equiv> (pointsEqual A P \<and> pointsEqual B R)"
lemma betweenSegment[intro]: "p isBetween A B \<longrightarrow> segment A B"
by (simp add: isBetweenPointsDistinct segment_def)


(*left corner of the segment*)
definition leftPSegment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "xCoord A \<noteq> xCoord B \<Longrightarrow> leftPSegment A B \<equiv> (if (leftFrom A B) then A else B)"
(*right corner of the segment*)
definition rightPSegment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "xCoord A \<noteq> xCoord B \<Longrightarrow> rightPSegment A B \<equiv> (if (leftFrom A B) then B else A)"
lemma leftPNotEqualRightP : "xCoord A \<noteq> xCoord B \<Longrightarrow> leftPSegment A B \<noteq> rightPSegment A B"
  by (auto simp add: rightPSegment_def leftPSegment_def)
lemma leftPRightPSimp[simp]: "xCoord p \<noteq> xCoord q \<Longrightarrow> p = leftPSegment p q \<Longrightarrow>
  q = rightPSegment p q"
  by (auto simp add: leftPSegment_def rightPSegment_def)
lemma leftPRightPSimp1[simp]: "xCoord p \<noteq> xCoord q \<Longrightarrow> q = rightPSegment p q \<Longrightarrow>
  p = leftPSegment p q"
  by (auto simp add: leftPSegment_def rightPSegment_def)
lemma leftPRightPSimp2[simp]: "leftFrom P Q \<Longrightarrow> P = leftPSegment P Q"
  by (auto simp add: leftFrom_def leftPSegment_def)
lemma leftPRightPSimp3[simp]: "leftFrom P Q \<Longrightarrow> Q = rightPSegment P Q"
  by (auto simp add: leftFrom_def)

(*Point p is on segment AB*)
(*pointOnSegment and signedArea*)
(*wenn ein Punkt von AB auf einer geraden PR (und ungleich mit Ecken),
  dann trennt AB die Ecken P und R*)
lemma pointOnSegment_noRightTurn : "segment P R \<Longrightarrow> A \<noteq> P \<Longrightarrow> A \<noteq> R \<Longrightarrow> A isBetween P R \<Longrightarrow>
  rightTurn A B P \<Longrightarrow> rightTurn A B R \<Longrightarrow> False"
  by (smt collinearTransitiv conflictingRightTurns2 leftRightTurn leftTurnsImplyBetween notBetween
  notRightTurn pointsEqualSame rightTurnRotate2 segment_def swapBetween)
lemma pointOnSegment_noRightTurn1 : "segment P R \<Longrightarrow> A \<noteq> P \<Longrightarrow> A \<noteq> R \<Longrightarrow> B isBetween P R \<Longrightarrow>
  rightTurn A B P \<Longrightarrow> rightTurn A B R \<Longrightarrow> False"
  by (meson isBetweenImpliesCollinear3 leftRightTurn leftTurnRotate2 leftTurnsImplyBetween
  newLeftTurn notBetween3)


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
lemma notSelfCrossing [simp]: "\<not>crossing A B A B" by (simp add: crossing_def)

(*intersection, even if endpoint is on segment*)
definition intersect :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<equiv> crossing A B P R \<or>
  P isBetween A B \<or> R isBetween A B \<or> A isBetween P R \<or> B isBetween P R"
(*lemma intersectSame [simp]: "segment A B \<Longrightarrow> intersect A B A B"
  by (simp add: intersect_def isBetween_def pointOnSegment_def pointsEqualArea segment_def)*)

lemma crossingIntersect [simp]: "crossing A B P R \<Longrightarrow> intersect A B P R"
  apply (simp add: intersect_def)
done
lemma intersectSym[simp]: "segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R = intersect B A P R"
  using crossingSym intersect_def segment_def by auto
lemma intersectSym1 : "segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R = intersect P R A B"
  using crossingSym1 intersect_def by auto


(*if the segments AB and PR intersect, then both corners of PR can not be on the same side of AB*)
lemma intersectRightTurn: "segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<Longrightarrow>
  rightTurn A B P \<and> rightTurn A B R \<Longrightarrow> False"
  apply (simp only: intersect_def, auto)
  using rightTurnRotate2 apply blast
  using rightTurnRotate2 apply blast
  apply (metis conflictingRigthTurns1 pointOnSegment_noRightTurn rightTurnRotate2)
by (metis leftRightTurn leftTurnDiffPoints pointOnSegment_noRightTurn1)
  

lemma intersectRightTurn1 : "segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<Longrightarrow>
  rightTurn A R P \<and> rightTurn P B R \<Longrightarrow> False"
  apply (simp only:intersect_def, safe)
  apply (metis crossingRightTurn crossingSym crossingSym1 rightTurnRotate2)
  apply (metis intersectRightTurn intersect_def rightTurnRotate2 segment_Sym)
  apply (metis intersectRightTurn intersect_def rightTurnRotate2 segment_Sym)
  using collSwap isBetweenImpliesCollinear apply blast
by (metis conflictingRightTurns2  swapBetween rightTurnRotate2)
  

(*additional Lemmas for intersect*)
lemma intersectNotCollinear: "segment a b \<Longrightarrow> segment c d \<Longrightarrow> intersect a b c d \<Longrightarrow>
  \<not>collinear a b c \<Longrightarrow> a \<noteq> c \<and> b \<noteq> c "
  by (simp add: intersect_def, metis notCollThenDiffPoints)
lemma intersectNotCollinear1: "segment a b \<Longrightarrow> segment c d \<Longrightarrow> intersect a b c d \<Longrightarrow>
  \<not>collinear d c b \<Longrightarrow> \<not>collinear a c b  \<Longrightarrow> rightTurn a d b \<Longrightarrow> rightTurn a c b \<Longrightarrow> False"
  apply (simp add: intersect_def, safe)
  using lineSeparate_def apply auto[1]
  using collRotate isBetweenImpliesCollinear apply blast
  apply (meson collRotate notRightTurn isBetweenImpliesCollinear)
  apply (metis conflictingRigthTurns leftRightTurn newLeftTurn1 notCollThenLfOrRt1)
by (smt intersectRightTurn intersect_def leftRightTurn notRightTurn notRightTurn1 segment_Sym)
lemma "segment a b \<Longrightarrow> segment c d \<Longrightarrow> collinear a b m \<Longrightarrow> collinear c d m \<Longrightarrow> intersect a b c d"
  apply (auto simp add: intersect_def)
  apply (case_tac "collinear a b c")
oops

lemma intersectBetween: "segment A B \<Longrightarrow> segment B C \<Longrightarrow> A isBetween B C \<Longrightarrow> intersect A B B C"
  by (simp add: intersect_def)

(*definition intersect :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<equiv> intersectS A B P R
    \<and> (A = P \<longrightarrow> pointOnSegment B P R \<or> pointOnSegment R A B)
    \<and> (B = R \<longrightarrow> pointOnSegment A P R \<or> pointOnSegment P A B)
    \<and> (A = R \<longrightarrow> pointOnSegment B P R \<or> pointOnSegment P A B)
    \<and> (B = P \<longrightarrow> pointOnSegment A P R \<or> pointOnSegment R A B)"
lemma intersectedSame[simp]: "segment A B \<Longrightarrow> intersect A B A B"
  by (auto simp add: intersect_def)
lemma intersectedSym: "segment A B \<Longrightarrow> segment P R \<Longrightarrow>
  intersect A B P R = intersect P R A B"
  apply (rule iffI, simp add: intersect_def, (erule conjE)+)
  using intersectSym1 apply blast
  apply (simp add: intersect_def, (erule conjE)+)
using intersectSym1 by blast
lemma intersectedAdjSym1: "segment A B \<Longrightarrow> segment P R \<Longrightarrow>
  intersect A B P R = intersect B A P R"
  apply (subgoal_tac "segment B A")
  apply (rule iffI, simp add: intersect_def, (erule conjE)+)
  using intersectSym pointOnSegmentSym apply blast
  apply (simp add: intersect_def, (erule conjE)+)
  using intersectSym pointOnSegmentSym apply blast
using segment_Sym by blast*)

(*definition notIntersectAdj :: "[point2d,point2d,point2d,point2d] \<Rightarrow> bool" where
  "notIntersectAdj A B P R \<equiv> (A = P \<longrightarrow> \<not>collinear B P R) \<and> (A = R \<longrightarrow> \<not>collinear B P R)
  \<and> (B = P \<longrightarrow> \<not>collinear A P R) \<and> (B = R \<longrightarrow> \<not>collinear A P R)
  \<and> (A \<noteq> P \<and> A \<noteq> R \<and> B \<noteq> P \<and> B \<noteq> R \<longrightarrow> \<not>intersect A B P R)"*)

(*evtl. noch nützrlich*)
(*lemma pointOnSegmentEQ : "segment a c \<Longrightarrow> pointOnSegment b a c = (collinear a b c \<and>
  (\<exists> d. signedArea a c d \<noteq> 0) \<and> (\<forall> d. signedArea a c d \<noteq> 0 \<longrightarrow>
  (0 < (signedArea a b d / signedArea a c d) \<and> (signedArea a b d / signedArea a c d) \<le> 1 )))"
  apply (auto simp add: pointOnSegment_def isBetween_def)
  apply (simp add: pointsEqualArea segment_def, simp add: pointsEqualArea segment_def)
  apply (erule_tac x=da in allE, auto)
oops*)
(*formalizing Analytic Geometries. Pasch's axiom*)
(*lemma paschAxiom: "segment A C \<Longrightarrow> segment B C \<Longrightarrow> segment P B \<Longrightarrow> segment Q A \<Longrightarrow>
  pointOnSegment P A C \<Longrightarrow> pointOnSegment Q B C \<Longrightarrow>
  (\<exists> X. pointOnSegment X P B \<and> pointOnSegment X Q A)"
  apply (case_tac "A = C")
    apply (subgoal_tac "P = A")
    apply (rule_tac x="P" in exI, auto)
    apply (simp add: segment_def)
  apply (case_tac "B = C")
    apply (subgoal_tac "B = Q")
    apply (rule_tac x="P" in exI, simp add: segment_def)
    apply (simp add: segment_def)
  apply (case_tac "C = P")
    apply (rule_tac x="Q" in exI)
    using pointOnSegment_def apply auto[1]
  apply (case_tac "C = Q")
    apply (rule_tac x="P" in exI)
    using pointOnSegment_def apply auto[1]
  apply (case_tac "A = B")
    apply (rule_tac x="B" in exI)
    using pointOnSegment_def apply auto[1]
  apply (case_tac "collinear A C B")
    apply (subgoal_tac "collinear A P Q")
    apply (case_tac "C isBetween A B")
      apply (rule_tac x="C" in exI)
      apply (rule conjI)
      apply (simp add: isBetweenImpliesCollinear leftTurn_def leftTurnsImplyBetween notBetween2 
        pointOnSegment_def pointsEqualArea rightTurn_def)
      apply (smt collRotate collinearTransitiv collinearTransitiv2 colliniearRight
        isBetweenImpliesCollinear3 isBetweenPointsDistinct leftTurnsImplyBetween notBetween3
        notLeftTurn swapBetween)
      apply (simp add: isBetweenImpliesCollinear leftTurn_def leftTurnsImplyBetween notBetween2 
        pointOnSegment_def pointsEqualArea rightTurn_def)
      apply (smt collRotate collinearTransitiv collinearTransitiv2 colliniearRight
        isBetweenImpliesCollinear3 isBetweenPointsDistinct leftTurnsImplyBetween notBetween3
        notLeftTurn swapBetween)
    apply (case_tac "B isBetween A C")
      apply (rule_tac x="B" in exI)
      apply (rule conjI)
      apply (simp add: isBetweenImpliesCollinear leftTurn_def leftTurnsImplyBetween notBetween2
        pointOnSegment_def pointsEqualArea rightTurn_def)
      apply (simp add: isBetweenImpliesCollinear leftTurn_def leftTurnsImplyBetween notBetween  pointOnSegment_def pointsEqualArea rightTurn_def)
      apply (smt collRotate collinearTransitiv2 colliniearRight isBetweenImpliesCollinear3 leftTurnsImplyBetween notBetween2 notLeftTurn signedAreaRotate swapBetween)
      apply (simp add: isBetweenImpliesCollinear  leftTurn_def leftTurnsImplyBetween
        notBetween2  pointOnSegment_def pointsEqualArea rightTurn_def)
      apply (smt collRotate collinearTransitiv2 colliniearRight isBetweenImpliesCollinear3
        leftTurnsImplyBetween notBetween2 notLeftTurn signedAreaRotate swapBetween)
    apply (simp add: collinearTransitiv collinearTransitiv2 collinear_def
      isBetweenImpliesCollinear3 pointOnSegment_def)
    apply (metis cancel_comm_monoid_add_class.diff_cancel collinearTransitiv collinearTransitiv2
      collinear_def isBetweenImpliesCollinear3 mult.commute mult_zero_right)
  (*echter schnitt*)
oops*)

(*theorem crossingEq1: "segment A B \<Longrightarrow> segment P Q \<Longrightarrow> crossing A B P Q \<Longrightarrow>
  \<exists> X .X isBetween A B \<and> X isBetween P Q"
  apply (simp add: crossing_def, safe)
  apply (simp add: lineSeparate_def, safe)
  using interiority leftRightTurn apply blast
oops*)

(*theorem intersectionEq1: "segment A B \<Longrightarrow> segment P Q \<Longrightarrow> intersect A B P Q \<Longrightarrow> \<exists> X .pointOnSegment X A B \<and>
  pointOnSegment X P Q"
  apply (case_tac "A = P")using intersect_def notCollThenDiffPoints pointOnSegment_def apply blast
  apply (case_tac "A = Q")using intersect_def notCollThenDiffPoints pointOnSegment_def apply blast
  apply (case_tac "B = P")using intersect_def notCollThenDiffPoints pointOnSegment_def apply blast
  apply (case_tac "B = Q")using intersect_def notCollThenDiffPoints pointOnSegment_def apply blast
  apply (case_tac "collinear A B P")
    apply (meson crossingCollinear intersect_def pointOnSegmentSelf pointOnSegmentSelf1)
  apply (case_tac "collinear A B Q")
    apply (metis conflictingLeftTurns3 conflictingRightTurns3 crossing_def intersect_def
      lineSeparate_def pointOnSegmentSelf pointOnSegmentSelf1)
  apply (case_tac "collinear P Q A")
    apply (metis conflictingLeftTurns3 conflictingRightTurns3 crossing_def intersect_def
      lineSeparate_def pointOnSegmentSelf pointOnSegmentSelf1)
  apply (case_tac "collinear P Q B")
    apply (metis conflictingLeftTurns3 conflictingRightTurns3 crossing_def intersect_def
      lineSeparate_def pointOnSegmentSelf pointOnSegmentSelf1)
  apply (subgoal_tac "\<exists>X. collinear X A B \<and> collinear X P Q")
  apply (smt isBeetweenOrient leftTurnRotate2 notLeftTurn notRightTurn1)
  apply (subgoal_tac "\<exists> X. leftTurn Q X A \<and> rightTurn Q X B \<and> leftTurn A X P \<and> rightTurn A X Q")
oops
lemma intersectionEq2: "segment A B \<Longrightarrow> segment P Q \<Longrightarrow> \<exists> X .pointOnSegment X A B \<and>
  pointOnSegment X P Q \<Longrightarrow> intersect A B P Q "
  apply (case_tac "A = P")using intersect_def notCollThenDiffPoints pointOnSegment_def apply blast
  apply (case_tac "A = Q")using intersect_def notCollThenDiffPoints pointOnSegment_def apply blast
  apply (case_tac "B = P")using intersect_def notCollThenDiffPoints pointOnSegment_def apply blast
  apply (case_tac "B = Q")using intersect_def notCollThenDiffPoints pointOnSegment_def apply blast
  apply (case_tac "collinear A B P")
oops
theorem intersectionEq: "segment A B \<Longrightarrow> segment P Q \<Longrightarrow> (\<exists> X .pointOnSegment X A B \<and>
  pointOnSegment X P Q) = intersect A B P Q "  
oops*)

end
