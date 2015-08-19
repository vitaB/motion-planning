theory point
imports Complex_Main (*"~~/src/HOL/Library/Old_Datatype.thy"*)
begin

(*References
[1] "Automation for Geometry in Isabelle/HOL", Laura Meikle*)

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
lemma leftFromPointDest [dest]: "leftFromPoint a b \<Longrightarrow> leftFromPoint b a \<Longrightarrow> False"
  by (simp add: leftFromPoint_def)

(*signed area of a triangle; with the convention being that
- if the points are ordered anti-clockwise, the area is positive
- if the points are ordered clockwise, the area is negative.*)
definition signedArea :: "[point2d, point2d, point2d] \<Rightarrow> real" where(*[1]*)
"signedArea a b c \<equiv> (xCoord b - xCoord a)*(yCoord c - yCoord a)
- (yCoord b - yCoord a)*(xCoord c - xCoord a)"
lemma signedAreaRotate [simp]: "signedArea b c a = signedArea a b c"(*[1]*)
  by (simp add: signedArea_def, algebra)
lemma signedAreaRotate2 [simp]: "signedArea b a c = signedArea a c b"(*[1]*)
  by (simp add: signedArea_def,  algebra)
lemma areaDoublePoint [simp]: "signedArea a a b = 0"(*[1]*) by (simp add: signedArea_def)
lemma areaDoublePoint2 [simp]: "signedArea a b b = 0"(*[1]*) by (simp add: signedArea_def)
  
(*3 points are on a line*)
definition collinear :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where(*[1]*)
  "collinear a b c \<equiv>
    ((xCoord a - xCoord b)*(yCoord b - yCoord c) = (yCoord a- yCoord b)*(xCoord b - xCoord c))"
lemma colliniearRight : "collinear a b c = (signedArea a b c = 0)"
  by (simp add: collinear_def signedArea_def, rule iffI, algebra+)
(*degenerate cases where the points may be collinear,
or equivalently, the area of the triangle they define is zero:*)
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
lemma conflictingLeftTurns [dest]: "leftTurn a b c \<Longrightarrow> leftTurn a c b \<Longrightarrow> False"(*[1]*) by (metis notLeftTurn) 
lemma conflictingLeftTurns3 [dest]: "leftTurn a b c \<Longrightarrow> collinear a b c \<Longrightarrow> False"(*[1]*)
  by (metis collSwap notLeftTurn)
lemma conflictingRigthTurns [dest]: "rightTurn a b c \<Longrightarrow> rightTurn a c b \<Longrightarrow> False" by (metis notRightTurn) 
lemma conflictingRigthTurns1 [dest]: "rightTurn a b c \<Longrightarrow> rightTurn b a c \<Longrightarrow> False"
  by (metis leftRightTurn notLeftTurn)
lemma conflictingRightTurns2 [dest]: "rightTurn a b c \<Longrightarrow> collinear a b c \<Longrightarrow> False"
  by (metis collSwap notRightTurn)

(*lemmas for collinear und signedArea*)
lemma notCollThenDiffPoints [intro]: "\<not>collinear a b c \<Longrightarrow> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"(*[1]*) by (auto)
lemma notCollThenLfOrRt1 [intro]: "\<not>collinear a b c \<Longrightarrow> leftTurn a b c \<or> rightTurn a b c" by (auto)
lemma areaContra [dest]: " signedArea a c b < 0 \<Longrightarrow> signedArea a b c < 0  \<Longrightarrow> False"(*[1]*)
  by (metis colliniearRight leftTurn_def less_trans notLeftTurn) 
lemma areaContra2 [dest]: "0 < signedArea a c b\<Longrightarrow> 0 < signedArea a b c \<Longrightarrow> False"(*[1]*)
  by (metis leftTurn_def notLeftTurn) 
lemma collinearTransitiv1 : "\<exists> a. collinear a b c \<and> collinear a b d \<longrightarrow> collinear a c d"
  by (simp add: colliniearRight, rule_tac x=d in exI, simp)


(*A point between B and C*)
definition midpoint :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"midpoint a b c = (2 * yCoord a = yCoord b + yCoord c \<and> 2 * xCoord a = xCoord b + xCoord c)"
lemma midPointCollinear : "midpoint a b c \<Longrightarrow> collinear a b c"
  by (auto simp add: midpoint_def collinear_def, algebra)
lemma midPointSym : "midpoint a b c = midpoint a c b" by (auto simp add: midpoint_def)
lemma midpointNotSame: "b\<noteq>c \<Longrightarrow> midpoint a b c \<Longrightarrow> midpoint b a c \<Longrightarrow> False"
 by (auto simp add: midpoint_def, smt pointsNotEqual1)






(*Lemmas und Definitionen, die momentan nicht gebraucht werden*)
(*Punkte sind gleich, wenn*)
(*lemma pointsEqualRight: "a \<noteq> b = (\<exists> d. signedArea a b d \<noteq> 0)"
  apply (auto)
  apply (rule ccontr)
  apply (simp, erule_tac x=d in allE)
  apply (simp)
sorry
(*mögliche Definitionen für isBetween. Nochmal anschauen!*)
definition isBetween :: "[point2d, point2d, point2d] \<Rightarrow> bool" where(*[1]*)
" isBetween b a c \<equiv> collinear a b c \<and> (\<exists> d. signedArea a c d \<noteq> 0) \<and>
(\<forall> d. signedArea a c d \<noteq> 0 \<longrightarrow>
(0 < (signedArea a b d / signedArea a c d) \<and> (signedArea a b d / signedArea a c d) < 1 ))"
lemma swapIsBetween [simp]: "isBetween a c b = isBetween a b c" (*[1]*)
  apply (simp add: isBetween_def, safe)
  apply (rule_tac x=d in exI, metis collSwap colliniearRight)
  apply (erule_tac x=da in allE)
sorry
lemma notIsBetweenSamePoint [dest]: "isBetween a b b \<Longrightarrow> False"(*[1]*)
  by (simp add: isBetween_def)
lemma isBetweenCollinear [intro] : "isBetween a b c \<longrightarrow> collinear a b c"(*[1]*)
  by (simp add: isBetween_def)
lemma isBetweenCollinear2 [intro] : "isBetween b a c \<longrightarrow> collinear a b c"(*[1]*)
  by (simp add: isBetween_def)
lemma isBetweenCollinear3 [intro] : "isBetween c a b \<longrightarrow> collinear a b c"(*[1]*)
  by (simp add: isBetween_def)
lemma notIsBetweenSelf [simp]: "\<not> (isBetween a a b)"(*[1]*)
  by (rule notI, auto simp add: isBetween_def)
lemma isBetweenPointsDistinct [intro]: "isBetween a b c \<Longrightarrow> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"(*[1]*)
  by (auto simp add: isBetween_def) 
lemma onePointIsBetween [intro]: "collinear a b c \<Longrightarrow>
  isBetween a b c \<or> isBetween b a c \<or> isBetween c a b"(*[1]*)
  apply (safe)
sorry
lemma notBetween [dest]: "\<lbrakk>isBetween A B C;isBetween B A C\<rbrakk>  \<Longrightarrow> False" (*[1]*)
  using onePointIsBetween twoPointsColl by blast
lemma notBetween2 [dest]: "\<lbrakk>isBetween A B C ;isBetween C A B\<rbrakk>  \<Longrightarrow> False"(*[1]*)
  using onePointIsBetween twoPointsColl by blast
lemma notBetween3 [dest]: "\<lbrakk>isBetween B A C ;isBetween C A B\<rbrakk> \<Longrightarrow> False"(*[1]*)
  using onePointIsBetween twoPointsColl by blast
*)
(*
definition betwpoint :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"betwpoint a b c = (\<forall> n. n > 1 \<longrightarrow> (n * yCoord a = yCoord b + yCoord c \<and> n * xCoord a = xCoord b + xCoord c))"
lemma swapBetween [simp]: "betwpoint a c b = betwpoint a b c" by(auto simp add: betwpoint_def)
(*lemma notBetweenSamePoint [dest]: "betwpoint a b b \<Longrightarrow> False"
  apply (simp add: betwpoint_def)
  apply (erule_tac x = 2 in allE)
  apply (auto)
oops*)
lemma betwpointCollinear [intro] : "betwpoint a b c \<longrightarrow> collinear a b c"
  apply (rule impI, simp add: betwpoint_def collinear_def)
  apply (erule_tac x = 2 in allE, simp, algebra)
done
lemma betwpointCollinear2 [intro] : "betwpoint b a c \<longrightarrow> collinear a b c"
  apply (rule impI, simp add: betwpoint_def collinear_def)
  apply (erule_tac x = 2 in allE, simp, algebra)
done
lemma betwpointCollinear3 [intro] : "betwpoint c a b \<longrightarrow> collinear a b c"
  apply (rule impI, simp add: betwpoint_def collinear_def)
  apply (erule_tac x = 2 in allE, simp, algebra)
done
(*lemma "collinear a b c = betwpoint a b c \<or> betwpoint b a c \<or> betwpoint c a b"
  apply (rule iffI, simp add: collinear_def) apply (auto)
  apply (simp add: collinear_def betwpoint_def)
  apply (rule allI)
oops*)
lemma conflictingLeftTurns2 [dest]: "leftTurn a b c \<Longrightarrow> betwpoint a b c \<Longrightarrow> False"
  by (metis betwpointCollinear notLeftTurn swapBetween) 
*)

(*lemma collinearTransitiv : "a \<noteq> b \<Longrightarrow> collinear a b c \<Longrightarrow> collinear a b d \<Longrightarrow> collinear a c d"
  apply (simp add: colliniearRight)
  apply (cases "a = c", simp, cases "a = d", simp)
  apply (cases "c = d", simp, cases "c = b", simp)
  apply (cases "b = d", metis collSwap colliniearRight) 
  apply (rule ccontr, subgoal_tac "signedArea a c d > 0 \<or> signedArea a c d < 0", safe, simp)
  apply (simp add: signedArea_def)
sorry
lemma collinearOrient :"a \<noteq> b \<Longrightarrow> a \<noteq> c \<Longrightarrow>a \<noteq> d \<Longrightarrow>
  collinear a b c \<Longrightarrow> collinear a b d \<Longrightarrow> (leftTurn a c e \<and> leftTurn a d e) \<or> (rightTurn a c e \<and> rightTurn a d e)
  \<or> (collinear a c e \<and> collinear a d e)"
  apply (subgoal_tac " collinear a c d", simp add: colliniearRight)
  apply (cases "a = e")
  apply (cases "e = c")
  apply (cases "e = d", simp)
sorry*)
(*lemma notBetweenSelf [simp]: "\<not> (betwpoint a a b)"
  apply (rule notI)
  apply (simp add: betwpoint_def)
  apply (cut_tac  r=a and p=b in pointsNotEqual)
  apply (erule_tac x = 1 in allE) apply (simp)
  apply (auto)
oops*)
end
