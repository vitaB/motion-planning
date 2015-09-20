theory point
imports Complex_Main (*"~~/src/HOL/Library/Old_Datatype.thy"*)
begin

(*References
[1] "Automation for Geometry in Isabelle/HOL", Laura Meikle
[2] Intuition in Formal Proof: A Novel Framework for Combining Mathematical Tools, Laura Meikle*)

(*defintion for Points*)
typedef point2d = "{p::(real*real). True}" by(auto)(*[1]*)
definition xCoord :: "point2d \<Rightarrow> real" where "xCoord P \<equiv> fst(Rep_point2d P)"(*[1]*)
definition yCoord :: "point2d \<Rightarrow> real" where "yCoord P \<equiv> snd(Rep_point2d P)"(*[1]*)
lemma xCoord[simp]: "xCoord (Abs_point2d (a, b)) = a" by (simp add: xCoord_def Abs_point2d_inverse)
lemma yCoord[simp]: "yCoord (Abs_point2d (a, b)) = b" by (simp add: yCoord_def Abs_point2d_inverse)
lemma pointSameCoord [simp]: "Abs_point2d(a, b) = Abs_point2d(a', c) \<longleftrightarrow> a = a' \<and> b = c"
  by (metis (full_types) Abs_point2d_inject fst_conv mem_Collect_eq snd_conv)


(*points equal*)
definition pointsEqual :: "point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "pointsEqual r p = (xCoord r = xCoord p \<and> yCoord r = yCoord p)"
lemma pointsNotEqual : "\<not>pointsEqual r p = (xCoord r \<noteq> xCoord p \<or> yCoord r \<noteq> yCoord p)"
  by (simp add: pointsEqual_def)
lemma pointsNotEqual1: "(xCoord r \<noteq> xCoord p \<or> yCoord r \<noteq> yCoord p) \<longleftrightarrow> r \<noteq> p"
  by (metis Rep_point2d_inverse prod.collapse xCoord_def yCoord_def)
lemma pointsEqualSame : "pointsEqual p p" by (simp add: pointsEqual_def)
theorem pointsEqual1 [simp] : "pointsEqual p r = (p = r)"
  apply (auto simp add: pointsEqual_def)
by (metis Rep_point2d_inverse prod.collapse xCoord_def yCoord_def)


(*Point a left from point B*)
definition leftFromPoint :: "point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "leftFromPoint a b = (xCoord a < xCoord b)"
lemma leftFromPointSimp: "xCoord a \<noteq> xCoord b \<Longrightarrow> \<not>leftFromPoint a b \<Longrightarrow> leftFromPoint b a"
  by(simp add: leftFromPoint_def)
lemma leftFromPointDest [dest]: "leftFromPoint a b \<Longrightarrow> leftFromPoint b a \<Longrightarrow> False"
  by (simp add: leftFromPoint_def)

(*signed area of a triangle; with the convention being that
- if the points are ordered anti-clockwise, the area is positive
- if the points are ordered clockwise, the area is negative.*)
definition signedArea :: "[point2d, point2d, point2d] \<Rightarrow> real" where(*[1]*)
  "signedArea a b c \<equiv> (xCoord b - xCoord a)*(yCoord c - yCoord a)
    - (yCoord b - yCoord a)*(xCoord c - xCoord a)"
lemma signedAreaMin: "signedArea A B C = -signedArea A C B"
  by (simp add: signedArea_def)
lemma signedAreaRotate [simp]: "signedArea b c a = signedArea a b c"(*[1]*)
  by (simp add: signedArea_def, algebra)
lemma signedAreaRotate2 [simp]: "signedArea b a c = signedArea a c b"(*[1]*)
  by (simp add: signedArea_def,  algebra)
lemma areaDoublePoint [simp]: "signedArea a a b = 0"(*[1]*) by (simp add: signedArea_def)
lemma areaDoublePoint2 [simp]: "signedArea a b b = 0"(*[1]*) by (simp add: signedArea_def)
lemma hausner: "signedArea P A B + signedArea P B C + signedArea P C A = signedArea A B C" (*[2]*)
  by (simp add: mult.commute right_diff_distrib' signedArea_def)

  
(*3 points are on a line*)
definition collinear :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where(*[1]*)
  "collinear a b c \<equiv>
    ((xCoord a - xCoord b)*(yCoord b - yCoord c) = (yCoord a- yCoord b)*(xCoord b - xCoord c))"
lemma colliniearRight : "collinear a b c = (signedArea a b c = 0)"
  by (simp add: collinear_def signedArea_def, rule iffI, algebra+)
lemma collRotate [simp]: "collinear c a b = collinear a b c"(*[1]*)
  by (simp add: collinear_def, algebra)
lemma collSwap [simp]: "collinear a c b = collinear a b c"(*[1]*) by(simp add:collinear_def,algebra)
lemma twoPointsColl [simp]: "collinear a b b"(*[1]*) by (simp add: collinear_def)
lemma twoPointsColl2 [simp]: "collinear a a b"(*[1]*) by (simp add: collinear_def)

(*three points a, b and c make a left turn if they make an anti-clockwise cycle:*)
definition leftTurn :: "[point2d, point2d, point2d] \<Rightarrow> bool" where(*[1]*)
"leftTurn a b c \<equiv> 0 < signedArea a b c"
lemma leftTurnRotate [simp]: "leftTurn b c a = leftTurn a b c"(*[1]*) by (simp add: leftTurn_def)
lemma leftTurnRotate2 [simp]: "leftTurn b a c = leftTurn a c b"(*[1]*) by (simp add: leftTurn_def)
lemma leftTurnDiffPoints [intro]: "leftTurn a b c \<Longrightarrow> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"(*[1]*)
  by (auto simp add: leftTurn_def)

(*three points a, b and c make a right turn if they make an clockwise cycle:*)
definition rightTurn :: "[point2d, point2d, point2d] \<Rightarrow> bool" where
  "rightTurn a b c \<equiv> 0 > signedArea a b c"
lemma rightTurnEq: "rightTurn a b c = (signedArea a b c \<noteq> 0 \<and> \<not>leftTurn a b c)"
  using leftTurn_def rightTurn_def by auto
lemma leftRightTurn [simp]: "leftTurn a b c = rightTurn c b a"
  by (simp add: signedArea_def leftTurn_def rightTurn_def less_real_def mult.commute)
lemma rightTurnRotate [simp]: "rightTurn b c a = rightTurn a b c" by (simp add: rightTurn_def)
lemma rightTurnRotate2 [simp]: "rightTurn b a c = rightTurn a c b" by (simp add: rightTurn_def)

(*lemmas for leftTurn and rightTurn*)
lemma notLeftTurn [simp]: "(\<not> leftTurn a c b) = (leftTurn a b c \<or> collinear a b c)"(*[1]*)
  apply (simp add:leftTurn_def del: leftRightTurn, subst colliniearRight)
by (auto simp add: signedArea_def mult.commute)
lemma notRightTurn [simp]: "(\<not> rightTurn a c b) = (rightTurn a b c \<or> collinear a b c)"
  by (simp add: rightTurn_def, subst colliniearRight,auto simp add: signedArea_def mult.commute)
lemma notRightTurn1 [simp]: "(\<not> rightTurn a b c) = (leftTurn a b c \<or> collinear a b c)"
  by (metis leftRightTurn leftTurnRotate2 notLeftTurn)
lemma conflictingLeftTurns [dest]: "leftTurn a b c \<Longrightarrow> leftTurn a c b \<Longrightarrow> False"(*[1]*)
  by (metis notLeftTurn) 
lemma conflictingLeftTurns3 [dest]: "leftTurn a b c \<Longrightarrow> collinear a b c \<Longrightarrow> False"(*[1]*)
  by (metis collSwap notLeftTurn)
lemma conflictingRigthTurns [dest]: "rightTurn a b c \<Longrightarrow> rightTurn a c b \<Longrightarrow> False"
  by (metis notRightTurn) 
lemma conflictingRigthTurns1 [dest]: "rightTurn a b c \<Longrightarrow> rightTurn b a c \<Longrightarrow> False"
  by (metis leftRightTurn notLeftTurn)
lemma conflictingRightTurns3 [dest]: "rightTurn a b c \<Longrightarrow> collinear a b c \<Longrightarrow> False"
  by (metis collSwap notRightTurn)

(*signedArea Mult and Div *)
lemma leftTurnMult:"leftTurn a b c \<Longrightarrow> leftTurn d b e \<Longrightarrow> (signedArea a b c)*(signedArea d b e) > 0"
  using leftTurn_def by auto
lemma leftTurnDiv: "leftTurn a b c \<Longrightarrow> leftTurn d b e \<Longrightarrow> (signedArea a b c)/(signedArea d b e) > 0"
  using leftTurn_def by auto
lemma rightTurnMult: "rightTurn a b c \<Longrightarrow> rightTurn d b e \<Longrightarrow>
  (signedArea a b c)*(signedArea d b e) > 0"
  by (simp add: rightTurn_def zero_less_mult_iff)
lemma rightTurnDiv: "rightTurn a b c \<Longrightarrow> rightTurn d b e \<Longrightarrow>
  (signedArea a b c)/(signedArea d b e) > 0"
  by (simp add: rightTurn_def zero_less_divide_iff)
  
  

lemma interiority: "leftTurn t q r \<Longrightarrow> leftTurn p t r \<Longrightarrow> leftTurn p q t \<Longrightarrow> leftTurn p q r" (*[2]*)
  by (smt hausner leftRightTurn rightTurn_def)
(*nur mit cramersRule beweisbar?*)
lemma transitivity: "leftTurn t s p \<Longrightarrow> leftTurn t s q \<Longrightarrow> leftTurn t s r \<Longrightarrow> leftTurn t p q (*[2]*)
  \<Longrightarrow> leftTurn t q r \<Longrightarrow> leftTurn t p r"
sorry

(*lemmas for collinear und signedArea*)
lemma notCollThenDiffPoints [intro]: "\<not>collinear a b c \<Longrightarrow> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"(*[1]*) by (auto)
lemma notCollThenLfOrRt1 [intro]: "\<not>collinear a b c \<Longrightarrow> leftTurn a b c \<or> rightTurn a b c" by (auto)
lemma areaContra [dest]: " signedArea a c b < 0 \<Longrightarrow> signedArea a b c < 0  \<Longrightarrow> False"(*[1]*)
  by (metis colliniearRight leftTurn_def less_trans notLeftTurn) 
lemma areaContra2 [dest]: "0 < signedArea a c b\<Longrightarrow> 0 < signedArea a b c \<Longrightarrow> False"(*[1]*)
  by (metis leftTurn_def notLeftTurn) 
lemma collinearTransitiv1 : "\<exists> a. collinear a b c \<and> collinear a b d \<longrightarrow> collinear a c d"
  by (simp add: colliniearRight, rule_tac x=d in exI, simp)


(*mögliche Definitionen für isBetween.*)
definition isBetween :: "[point2d, point2d, point2d] \<Rightarrow> bool"
  ("_ isBetween _ _ " [60, 60, 60] 60) where(*[1]*)
  "b isBetween  a c \<equiv> collinear a b c \<and> (\<exists> d. signedArea a c d \<noteq> 0) \<and>
  (\<forall> d. signedArea a c d \<noteq> 0 \<longrightarrow>
  (0 < (signedArea a b d / signedArea a c d) \<and> (signedArea a b d / signedArea a c d) < 1 ))"
(*Punkte sind gleich, wenn*)
lemma pointsEqualArea: "a \<noteq> b = (\<exists> d. signedArea a b d \<noteq> 0)"
  apply (auto)
  apply (case_tac "xCoord a = xCoord b", rule_tac x="Abs_point2d(xCoord b + 1, yCoord b)" in exI)
    apply (metis Abs_point2d_inverse Collect_const Rep_point2d_inverse UNIV_I add_diff_cancel_left'
    eq_iff_diff_eq_0 mult.left_neutral mult_zero_left prod.collapse prod.sel(1) signedAreaRotate
    signedArea_def xCoord_def yCoord_def)
  apply (case_tac "yCoord a = yCoord b", rule_tac x="Abs_point2d(xCoord b, yCoord b + 1)" in exI)
    apply (simp add: signedArea_def)
  apply (case_tac "xCoord a < xCoord b", rule_tac x="Abs_point2d((xCoord b) + 1, yCoord b)" in exI)
    apply (simp add: signedArea_def)
  apply (rule_tac x="Abs_point2d((xCoord b) - 1, yCoord b)" in exI)
    apply (simp add: signedArea_def)
done
lemma "a \<noteq> b \<Longrightarrow>(\<exists> d c. leftTurn a b c \<and> leftTurn a b d \<and> signedArea a b c < signedArea a b d)"
  apply (case_tac "xCoord a = xCoord b")
    apply (rule_tac x="Abs_point2d(xCoord b - 2, yCoord b)" in exI,
      rule_tac x="Abs_point2d(xCoord b - 1, yCoord b)" in exI)
    
oops
lemma swapBetween1: "a isBetween c b \<Longrightarrow> a isBetween b c" (*[1]*)
  apply (simp add: isBetween_def, safe)
  apply (rule_tac x=d in exI, metis collSwap colliniearRight)
  apply (erule_tac x=da in allE, safe) using collSwap colliniearRight apply blast
  apply (simp add: colliniearRight divide_neg_neg le_divide_eq_1 left_diff_distrib' mult.commute
    signedArea_def)
  apply (simp add: divide_less_eq_1 divide_neg_neg right_diff_distrib')
  apply (smt divide_neg_neg divide_pos_pos)
  apply (erule_tac x=da in allE, safe) using collSwap colliniearRight apply blast
  apply (simp add: areaContra areaContra2 colliniearRight divide_le_0_iff divide_less_cancel
    divide_less_eq_1 left_diff_distrib' right_diff_distrib' signedArea_def)
  apply (simp add: mult.commute zero_less_divide_iff)
by smt
lemma swapBetween [simp]: "a isBetween c b = a isBetween b c" (*[1]*)
  by (auto simp add: swapBetween1)

lemma notBetweenSamePoint [dest]: "a isBetween b b \<Longrightarrow> False"(*[1]*)
  by (simp add: isBetween_def)
lemma isBetweenImpliesCollinear [intro] : "a isBetween b c \<longrightarrow> collinear a b c"(*[1]*)
  by (simp add: isBetween_def)
lemma isBetweenImpliesCollinear2 [intro] : "b isBetween a c \<longrightarrow> collinear a b c"(*[1]*)
  by (simp add: isBetween_def)
lemma isBetweenImpliesCollinear3 [intro] : "c isBetween a b \<longrightarrow> collinear a b c"(*[1]*)
  by (simp add: isBetween_def)
lemma notBetweenSelf [simp]: "\<not> (a isBetween a b)"(*[1]*)
  by (rule notI, auto simp add: isBetween_def)
lemma notBetweenSelf2 [simp]: "\<not> (b isBetween a b)"(*[1]*)
  by (rule notI, auto simp add: isBetween_def)

lemma isBetweenPointsDistinct [intro]: "a isBetween b c \<Longrightarrow> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"(*[1]*)
  by (auto simp add: isBetween_def) 
lemma conflictingLeftTurns2 [dest]: "leftTurn a b c \<Longrightarrow> a isBetween b c \<Longrightarrow> False" (*[1]*)
  using isBetween_def by auto
lemma conflictingRightTurns2 [dest]: "rightTurn a b c \<Longrightarrow> a isBetween b c \<Longrightarrow> False" (*[1]*)
  using isBetween_def by auto
lemma isBetweenTransitiv: "b isBetween a c \<Longrightarrow> d isBetween a b \<Longrightarrow> d isBetween a c"
  apply (auto simp add: isBetween_def)
  using colliniearRight apply auto[1]
  apply (smt zero_less_divide_iff)
by (smt divide_le_0_iff le_divide_eq_1)
lemma onePointIsBetween [intro]: "collinear a b c \<Longrightarrow> a \<noteq> b \<Longrightarrow> a \<noteq> c \<Longrightarrow> b \<noteq> c \<Longrightarrow> (*[2]*)
  a isBetween b c \<or> b isBetween a c \<or> c isBetween a b"
  apply (safe)
  apply (auto simp add: isBetween_def)
  apply (simp add: pointsEqualArea)+
sorry

lemma leftTurnsImplyBetween: "leftTurn A B C \<Longrightarrow> leftTurn A C D \<Longrightarrow> collinear B C D \<Longrightarrow>
  C isBetween B D" (*[2]*)
  apply (case_tac "B = D", blast, case_tac "C = B", blast, case_tac "C = D", blast)
  apply (case_tac "A = B", blast, case_tac "A = C") using leftTurnDiffPoints apply blast
  apply (case_tac "A = D") using leftTurnDiffPoints apply blast
  apply (simp add: isBetween_def)
  apply (safe)
  apply (simp add: pointsEqualArea)
  apply (subgoal_tac "signedArea d B C \<noteq> 0")
    apply (case_tac "signedArea d B D > 0", subgoal_tac "signedArea d B C > 0")
    using zero_less_divide_iff apply blast
sorry

lemma notBetween [dest]: "\<lbrakk>A isBetween B C; B isBetween A C\<rbrakk> \<Longrightarrow> False" (*[1]*)
  apply (auto simp add: isBetween_def)
  apply (case_tac "signedArea d B A \<noteq> 0")
    apply (erule_tac x=d in allE, simp)
    apply (erule_tac x=d in allE, safe, simp)
    apply (simp add: colliniearRight divide_less_eq_1 left_diff_distrib' right_diff_distrib'
      signedArea_def)
    apply (smt mult.commute)
    apply (simp add: divide_less_cancel divide_strict_right_mono_neg isBetween_def leftTurn_def
      leftTurnsImplyBetween rightTurn_def zero_less_divide_iff)
    apply (simp add: colliniearRight mult.commute right_diff_distrib' signedArea_def)
    apply (smt divide_less_eq_1_neg)
by (smt collSwap colliniearRight zero_less_divide_iff)
lemma notBetween2 [dest]: "\<lbrakk>A isBetween B C ; C isBetween A B\<rbrakk> \<Longrightarrow> False"(*[1]*)
  apply (auto simp add: isBetween_def)
  apply (case_tac "signedArea d B A \<noteq> 0")
    apply (erule_tac x=d in allE, simp)
    apply (erule_tac x=d in allE, safe, simp)
    apply (simp add: colliniearRight divide_less_eq_1 left_diff_distrib' right_diff_distrib'
      signedArea_def)
    apply (smt mult.commute)
    apply (simp add: divide_less_cancel divide_strict_right_mono_neg isBetween_def leftTurn_def
      leftTurnsImplyBetween rightTurn_def zero_less_divide_iff)
    apply (simp add: colliniearRight mult.commute right_diff_distrib' signedArea_def)
    apply (smt divide_less_eq_1_neg less_divide_eq_1_pos)
by (smt collSwap colliniearRight zero_less_divide_iff)
lemma notBetween3 [dest]: "\<lbrakk>B isBetween A C ; C isBetween A B\<rbrakk> \<Longrightarrow> False"(*[1]*)
  apply (auto simp add: isBetween_def)
  apply (case_tac "signedArea d A B \<noteq> 0")
    apply (erule_tac x=d in allE, simp)
    apply (erule_tac x=d in allE, safe, simp)
by (smt divide_le_0_iff divide_less_eq_1)

lemma collinearTransitiv: "a \<noteq> b \<Longrightarrow> collinear a b c \<Longrightarrow> collinear a b d \<Longrightarrow> collinear a c d"
  apply (simp add: colliniearRight)
  apply (cases "a = c", simp, cases "a = d", simp, cases "a = b", simp)
  apply (cases "c = d", simp, cases "c = b", simp)
  apply (cases "b = d", metis collSwap colliniearRight) 
  apply (rule ccontr, subgoal_tac "signedArea a c d > 0 \<or> signedArea a c d < 0", safe, simp)
  apply (simp add: signedArea_def)
sorry
lemma collinearTransitiv3: "a \<noteq> b \<Longrightarrow> collinear a b c \<Longrightarrow> collinear a b d \<Longrightarrow> collinear b c d"
  by (smt collRotate collinearTransitiv)

lemma collinearTransitiv2: "b \<noteq> c \<Longrightarrow> collinear a b c \<Longrightarrow> collinear b c d \<Longrightarrow> collinear a b d"
  using collRotate collinearTransitiv by blast

lemma newLeftTurn: "\<lbrakk>A isBetween C D; leftTurn A B C \<rbrakk> \<Longrightarrow> leftTurn B C D" (*[2]*)
  apply (subgoal_tac "signedArea B C D \<noteq> 0")
  apply (simp add: isBetween_def, safe)
  apply (erule_tac x=B in allE, simp)
  apply (smt divide_nonneg_nonpos leftTurn_def notLeftTurn notRightTurn1)
  apply (auto simp add: isBetween_def)
  apply (case_tac "signedArea d C D \<noteq> 0", erule_tac x=d in allE, simp)
  apply (metis areaDoublePoint collinearTransitiv2 colliniearRight notRightTurn1 signedAreaRotate)
by blast

lemma newLeftTurn1: "\<lbrakk>A isBetween C D; leftTurn A B C \<rbrakk> \<Longrightarrow> leftTurn D B A" (*[1]*)
  apply (subgoal_tac "rightTurn C B D")
  apply (smt collinearTransitiv2 isBetweenPointsDistinct leftTurnRotate2 newLeftTurn notLeftTurn swapBetween)
  apply (subgoal_tac "signedArea C B D \<noteq> 0")
  apply (simp only: isBetween_def, safe)
  apply (erule_tac x=B in allE, simp)
  apply (smt colliniearRight divide_nonneg_nonpos notRightTurn rightTurn_def)
  apply (auto simp add: isBetween_def)
  apply (case_tac "signedArea d C D \<noteq> 0", erule_tac x=d in allE, simp)
  apply (metis areaDoublePoint collinearTransitiv2 colliniearRight notRightTurn1 signedAreaRotate)
by blast





(*evtl. noch nützlich*)
(*A point between B and C*)
(*definition midpoint :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"midpoint a b c = (2 * yCoord a = yCoord b + yCoord c \<and> 2 * xCoord a = xCoord b + xCoord c)"*)
definition midpoint :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" 
  ("_ midpoint _ _ " [60, 60, 60] 60) where
  "d midpoint b c \<equiv> (signedArea d b c = 0 \<and> (\<forall> a. signedArea a b c = 2 * signedArea a b d))"
lemma midPointCollinear[simp]: "a midpoint b c \<Longrightarrow> collinear a b c"
  by (simp add: colliniearRight midpoint_def)
lemma midPointSym : "a midpoint b c = a midpoint c b"
  apply (auto simp add: midpoint_def)
by (metis collSwap colliniearRight notCollThenDiffPoints, smt hausner)+
lemma midpointNotSame1[dest]: "a \<noteq> b \<Longrightarrow> a midpoint a b \<Longrightarrow> False"
  by (simp add: midpoint_def pointsEqualArea)
lemma midpointNotSame[dest]: "b\<noteq>c \<Longrightarrow> a midpoint b c \<Longrightarrow> b midpoint a c \<Longrightarrow> False"
  apply (auto simp add: midpoint_def)
by (smt midPointSym midpointNotSame1 midpoint_def signedAreaMin)

lemma "(a midpoint b c) = (2 * yCoord a = yCoord b + yCoord c \<and> 2 * xCoord a = xCoord b + xCoord c)"
  apply (auto simp add: midpoint_def)
oops

lemma midpointPointExist: "\<exists> X. X midpoint a b"
  apply (case_tac "a=b", smt colliniearRight midpoint_def mult_zero_right notCollThenDiffPoints)
  apply (auto simp add: midpoint_def)
  apply (subgoal_tac "\<exists> d. signedArea a b d = 0", simp, erule_tac exE)
  apply (rule_tac x="d" in exI, auto)
oops

(*scalar multiplication*)
definition scalMult :: "[real, point2d] \<Rightarrow> point2d" (infixl "*s" 65) where (*[2]*)
  "a *s P \<equiv> (\<lambda>(p1,p2). Abs_point2d (a*p1,a*p2)) (Rep_point2d P)"
definition pointPlus :: "[point2d, point2d] \<Rightarrow> point2d" (infixl "+p" 60) where 
  "P +p Q \<equiv> Abs_point2d ((xCoord P) + (xCoord Q), (yCoord P) + (yCoord Q))"
lemma cramersRule: "signedArea P Q R = 0 \<Longrightarrow> T =
  ((signedArea T Q R / signedArea P Q R) *s P) +p
  ((signedArea P T R / signedArea P Q R) *s Q) +p
  ((signedArea P Q T / signedArea P Q R) *s R)"
oops


lemma CollPointExist: "\<exists> X. collinear A B X" by (rule_tac x=A in exI, auto)

lemma isBeetweenPointExist: "a \<noteq> b \<Longrightarrow> \<exists> X. X isBetween a b"
  apply (cut_tac a=a and b=b in midpointPointExist)
  apply (auto simp add: isBetween_def)
  apply (rule_tac x=X in exI)
  apply (safe)
  apply (simp add: pointsEqualArea)
  apply (simp add: pointsEqualArea)
  (*apply (subgoal_tac "collinear X a b")
    apply (case_tac "X = d", simp) using colliniearRight midPointCollinear apply blast
    apply (case_tac "X = a", simp, blast)
    apply (case_tac "X = b", simp)
    apply (case_tac "d = a", simp)
    apply (case_tac "d = b", simp)
    apply (case_tac "xCoord a = xCoord b", subgoal_tac "xCoord X = xCoord b")
      apply (case_tac "yCoord a < yCoord b", subgoal_tac "yCoord a < yCoord X \<and> yCoord X < yCoord b")
      apply (case_tac "signedArea d a b > 0")
      (*selbst hier kein Beweis*)*)
oops

definition segLength :: "point2d \<Rightarrow> point2d \<Rightarrow> real" where
  "segLength A B \<equiv> sqrt ((xCoord A - xCoord B)*(xCoord A - xCoord B) +
  (yCoord A - yCoord B)*(yCoord A - yCoord B))"
lemma segLengthSym: "segLength A B = segLength B A"
by (simp add: segLength_def, algebra)

definition quadArea :: "[point2d, point2d, point2d, point2d] \<Rightarrow> real" where
  "quadArea A B C D \<equiv> signedArea A B C + signedArea A C D"
lemma quadAreaSym: "quadArea A B C D = quadArea B C D A"
  by (auto simp add: quadArea_def signedArea_def, algebra)
lemma quadAreaSym1: "quadArea A B C D = quadArea C D A B"
  by (metis quadAreaSym)
lemma quadAreaSym2: "quadArea A B C D = quadArea D A B C"
  by (auto simp add: quadArea_def signedArea_def, algebra)

end