theory point
imports Complex_Main
begin

(*defintion von Punkten*)
typedef point2d = "{p::(real*real). True}" by(auto)
definition xCoord :: "point2d \<Rightarrow> real" where "xCoord P \<equiv> fst(Rep_point2d P)"
definition yCoord :: "point2d \<Rightarrow> real" where "yCoord P \<equiv> snd(Rep_point2d P)"
lemma [simp]: "xCoord (Abs_point2d (a, b)) = a" by (simp add: xCoord_def Abs_point2d_inverse)
lemma [simp]: "yCoord (Abs_point2d (a, b)) = b" by (simp add: yCoord_def Abs_point2d_inverse)

(*points equal*)
lemma pointSameCoord : "Abs_point2d(a, b) = Abs_point2d(a', c)\<Longrightarrow> a = a' \<and> b = c"
  by (auto, (metis Abs_point2d_inverse mem_Collect_eq fst_conv snd_conv)+)

definition pointsEqual :: "point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"pointsEqual r p \<longleftrightarrow> (xCoord r = xCoord p \<and> yCoord r = yCoord p)"
lemma pointsNotEqual : "\<not>pointsEqual r p \<longleftrightarrow> (xCoord r \<noteq> xCoord p \<or> yCoord r \<noteq> yCoord p)"
by (simp add: pointsEqual_def)
lemma pointsNotEqual1 [simp]: "(xCoord r \<noteq> xCoord p \<or> yCoord r \<noteq> yCoord p) \<longleftrightarrow> r \<noteq> p"
  by (metis Rep_point2d_inverse prod.collapse xCoord_def yCoord_def)
lemma pointsEqualSame : "pointsEqual p p" by (simp add: pointsEqual_def)
theorem pointsEqual1 [simp] : "pointsEqual p r \<longleftrightarrow> p = r"
  apply (rule iffI)
  apply (simp add: pointsEqual_def)
  apply (metis Rep_point2d_inverse prod.collapse xCoord_def yCoord_def)
  apply (simp add: pointsEqualSame)
done

(*Punkt a links vom Punkt b?*)
definition leftFromPoint :: "point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"leftFromPoint a b \<equiv> (xCoord a < xCoord b)"

(*signed area of a triangle; with the convention being that
- if the points are ordered anti-clockwise, the area is positive
- if the points are ordered clockwise, the area is negative.*)
definition signedArea :: "[point2d, point2d, point2d] \<Rightarrow> real" where
"signedArea a b c \<equiv> (xCoord b - xCoord a)*(yCoord c - yCoord a)
- (yCoord b - yCoord a)*(xCoord c - xCoord a)"
lemma signedAreaRotate [simp]: "signedArea b c a = signedArea a b c" by (simp add: signedArea_def, algebra)
lemma signedAreaRotate2 [simp]: "signedArea b a c = signedArea a c b" by (simp add: signedArea_def,  algebra)
lemma areaDoublePoint [simp]: "signedArea a a b = 0" by (simp add: signedArea_def)
lemma areaDoublePoint2 [simp]: "signedArea a b b = 0" by (simp add: signedArea_def)

(*three points a, b and c make a left turn if they make an anti-clockwise cycle:*)
definition leftTurn :: "[point2d, point2d, point2d] \<Rightarrow> bool" where
"leftTurn a b c \<equiv> 0 < signedArea a b c"
lemma leftTurnRotate [simp]: "leftTurn b c a = leftTurn a b c" by (simp add: leftTurn_def)
lemma leftTurnRotate2 [simp]: "leftTurn b a c = leftTurn a c b" by (simp add: leftTurn_def)
lemma leftTurnDiffPoints [intro]: "leftTurn a b c \<Longrightarrow> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"
by (auto simp add: leftTurn_def)


(*punkt A zwischen B und C*)
definition midpoint :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"midpoint a b c = (2 * yCoord a = yCoord b + yCoord c \<and> 2 * xCoord a = xCoord b + xCoord c)"
definition betwpoint :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"betwpoint a b c = (\<forall> n. n > 1 \<longrightarrow> (n * yCoord a = yCoord b + yCoord c \<and> n * xCoord a = xCoord b + xCoord c))"
lemma swapBetween [simp]: "betwpoint a c b = betwpoint a b c" by(auto simp add: betwpoint_def)
lemma notBetweenSamePoint [dest]: "betwpoint a b b \<Longrightarrow> False"
  apply (simp add: betwpoint_def)
  apply (erule_tac x = 2 in allE)
  apply (auto)
oops

(*3 Punkte sind auf einer geraden*)
definition collinear :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"collinear a b c = ((xCoord a - xCoord b)*(yCoord b - yCoord c) = (yCoord a- yCoord b)*(xCoord b - xCoord c))"
lemma "midpoint a b c \<longrightarrow> collinear a b c"
  apply (rule impI)
  apply (simp add: midpoint_def collinear_def)
  apply (erule conjE)
  apply algebra
done
lemma betwpointCollinear [intro] : "betwpoint a b c \<longrightarrow> collinear a b c"
  apply (rule impI)
  apply (simp add: betwpoint_def collinear_def)
  apply (erule_tac x = 2 in allE)
  apply (simp)
  apply algebra
done
lemma betwpointCollinear2 [intro] : "betwpoint b a c \<longrightarrow> collinear a b c"
  apply (rule impI)
  apply (simp add: betwpoint_def collinear_def)
  apply (erule_tac x = 2 in allE)
  apply (simp)
  apply algebra
done
lemma betwpointCollinear3 [intro] : "betwpoint c a b \<longrightarrow> collinear a b c"
  apply (rule impI)
  apply (simp add: betwpoint_def collinear_def)
  apply (erule_tac x = 2 in allE)
  apply (simp)
  apply algebra
done
lemma "collinear a b c \<longleftrightarrow> betwpoint a b c \<or> betwpoint b a c \<or> betwpoint c a b"
  apply (rule iffI)
  apply (simp add: collinear_def) apply (auto)
  apply (simp add: collinear_def betwpoint_def)
  apply (rule allI)
oops

(*degenerate cases where the points may be collinear, or equivalently, the area of the triangle they define is zero:*)
lemma colliniearRight : "collinear a b c \<longleftrightarrow> (signedArea a b c = 0)"
  apply (simp add: collinear_def signedArea_def)
  apply (rule iffI)
by algebra+
lemma collRotate [simp]: "collinear c a b = collinear a b c" by (simp add: collinear_def, algebra)
lemma collSwap [simp]: "collinear a c b = collinear a b c" by (simp add: collinear_def, algebra)
lemma twoPointsColl [simp]: "collinear a b b" by (simp add: collinear_def)
lemma twoPointsColl2 [simp]: "collinear a a b" by (simp add: collinear_def)

(*lemmas for leftTurn, collinear und signedArea*)
lemma notLeftTurn [simp]: "(\<not> leftTurn a c b) = (leftTurn a b c \<or> collinear a b c)"
  apply (simp add:leftTurn_def)
  apply (subst colliniearRight)
  apply (auto simp add: signedArea_def mult.commute)
done
lemma conflictingLeftTurns [dest]: "leftTurn a b c \<Longrightarrow> leftTurn a c b \<Longrightarrow> False" by (metis notLeftTurn) 
lemma conflictingLeftTurns2 [dest]: "leftTurn a b c \<Longrightarrow> betwpoint a b c \<Longrightarrow> False"
  by (metis betwpointCollinear notLeftTurn swapBetween) 
lemma conflictingLeftTurns3 [dest]: "leftTurn a b c \<Longrightarrow> collinear a b c \<Longrightarrow> False"
  by (metis collSwap notLeftTurn) 
lemma notCollThenDiffPoints [intro]: "\<not>collinear a b c \<Longrightarrow> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c" by (auto)
lemma areaContra [dest]: " signedArea a c b < 0\<Longrightarrow> signedArea a b c < 0  \<Longrightarrow> False"
  by (metis colliniearRight leftTurn_def less_trans notLeftTurn) 
lemma areaContra2 [dest]: "0 < signedArea a c b\<Longrightarrow> 0 < signedArea a b c \<Longrightarrow> False"
  by (metis leftTurn_def notLeftTurn) 

(*move/translate point*)






(*Zusätliche lemmas. alternative definition für isBetween. Nochmal anschauen!*)
lemma notBetweenSelf [simp]: "\<not> (betwpoint a a b)"
  apply (rule notI)
  apply (simp add: betwpoint_def)
  apply (cut_tac  r=a and p=b in pointsNotEqual)
  apply (erule_tac x = 1 in allE) apply (simp)
  apply (auto simp add: pointsEqual1)
oops
definition isBetween :: "[point2d, point2d, point2d] \<Rightarrow> bool" where (*a \<noteq> c ?*)
" isBetween b a c \<equiv> collinear a b c \<and> (\<exists> d. signedArea a c d \<noteq> 0) \<and>
(\<forall> d. signedArea a c d \<noteq> 0 \<longrightarrow>
0 < (signedArea a b d / signedArea a c d) \<and> (signedArea a b d / signedArea a c d) < 1 )"
lemma "isBetween a b c \<longleftrightarrow> betwpoint a b c"
  apply (rule iffI)
  apply (simp add: isBetween_def)
  apply (subst (asm) colliniearRight)
  apply (safe, erule_tac x=d in allE)
  apply (simp add: signedArea_def betwpoint_def)
oops
lemma notBetweenSelf [simp]: "\<not> (isBetween a a b)"
  by (rule notI, auto simp add: pointsEqual1 isBetween_def)
lemma isBetweenPointsDistinct [intro]: "isBetween a b c \<Longrightarrow> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"
  by (auto simp add: isBetween_def) 
lemma onePointIsBetween [intro]: "collinear a b c \<Longrightarrow>
isBetween a b c \<or> isBetween b a c \<or> isBetween c a b" sorry
lemma notBetween [dest]: "betwpoint A B C \<Longrightarrow>betwpoint B A C  \<Longrightarrow> False" sorry
lemma notBetween2 [dest]: "betwpoint A B C \<Longrightarrow>betwpoint C A B  \<Longrightarrow> False" sorry
lemma notBetween3 [dest]: "betwpoint B A C \<Longrightarrow>betwpoint C A B \<Longrightarrow> False" sorry

end
