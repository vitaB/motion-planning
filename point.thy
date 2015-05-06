theory point
imports Complex_Main
begin

(*defintion von Punkten*)
record point2d =
  xCoord :: real
  yCoord :: real

(*selectop von x des Punkts*)
definition getX :: "'a point2d_scheme \<Rightarrow> real" where "getX p \<equiv> xCoord p"
definition getY :: "'a point2d_scheme \<Rightarrow> real" where "getY p \<equiv> yCoord p"
lemma [simp]: "getX p = xCoord p" by (simp add: getX_def)
lemma [simp]: "getY p = yCoord p" by (simp add: getY_def)

(*update Points*)
definition setX :: "'a point2d_scheme \<Rightarrow> real \<Rightarrow> 'a point2d_scheme" where
"setX p a \<equiv> p\<lparr> xCoord := a\<rparr>"
definition setY :: "'a point2d_scheme \<Rightarrow> real \<Rightarrow> 'a point2d_scheme" where
"setY p a \<equiv> p\<lparr> yCoord := a\<rparr>"
definition incX :: "'a point2d_scheme \<Rightarrow> 'a point2d_scheme" where
"incX p \<equiv> \<lparr>xCoord = xCoord p + 1, yCoord = yCoord p,\<dots> = point2d.more p\<rparr>"
lemma "incX p = setX p (getX p + 1)" by (simp add: setX_def incX_def)

(*points equal*)
lemma pointSameCoord : "p\<lparr>xCoord := a\<rparr> = p\<lparr> xCoord := a'\<rparr> \<Longrightarrow> a = a'"
by (drule_tac f = xCoord in arg_cong, simp)
  (*apply (rule_tac r = p in point2d.cases_scheme) (*apply (cases p)*)
  apply (simp)*)
definition pointsEqual :: "point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"pointsEqual r p \<longleftrightarrow> (getX r = getX p \<and> getY r = getY p)"
lemma pointsNotEqual : " \<not>pointsEqual r p \<longleftrightarrow> (getX r \<noteq> getX p \<or> getY r \<noteq> getY p)"
by (simp add: pointsEqual_def) 
lemma pointsEqualSame : "pointsEqual p p" by (simp add: pointsEqual_def)
lemma pointsEqual : "pointsEqual p r \<longleftrightarrow> xCoord p = xCoord r \<and> yCoord p = yCoord r"
by (simp add: pointsEqual_def)
theorem pointsEqual1 : "pointsEqual p r \<longleftrightarrow> p = r"
  apply (rule iffI)
    apply (simp add: pointsEqual)
    apply (simp add: pointsEqualSame)
done

(*Punkt a links vom Punkt b?*)
definition leftFromPoint :: "point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"leftFromPoint a b = (getX a < getX b)"
lemma "a < b \<longleftrightarrow> leftFromPoint (| xCoord = a, yCoord = c |) (| xCoord = b, yCoord = c |)"
by (auto simp add: leftFromPoint_def)

(*As our verifications relied upon reasoning about the relative positions of points, we needed
to formlise this notion. For this we used the signed area of a triangle; with the convention being
that if the points are ordered anti-clockwise, the area is positive, and if the points are ordered
clockwise, the area is negative.*)
definition signedArea :: "[point2d, point2d, point2d] \<Rightarrow> real" where
"signedArea a b c \<equiv> (getX b - getX a)*(getY c - getY a)
- (getY b - getY a)*(getX c - getX a)"
lemma signedAreaRotate [simp]: "signedArea b c a = signedArea a b c"
  apply (simp add: signedArea_def) apply algebra
done
lemma signedAreaRotate2 [simp]: "signedArea b a c = signedArea a c b"
  apply (simp add: signedArea_def) apply algebra
done
lemma areaDoublePoint [simp]: "signedArea a a b = 0" by (simp add: signedArea_def)
lemma areaDoublePoint2 [simp]: "signedArea a b b = 0" by (simp add: signedArea_def)

(*Using this definition it was then easy to formally represent the orientation of points; we say
that three points a, b and c make a left turn if they make an anti-clockwise cycle:*)
definition leftTurn :: "[point2d, point2d, point2d] \<Rightarrow> bool" where
"leftTurn a b c \<equiv> 0 < signedArea a b c"
lemma leftTurnRotate [simp]: "leftTurn b c a = leftTurn a b c" by (simp add: leftTurn_def)
lemma leftTurnRotate2 [simp]: "leftTurn b a c = leftTurn a c b" by (simp add: leftTurn_def)
lemma leftTurnDiffPoints [intro]: "leftTurn a b c \<Longrightarrow> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"
by (auto simp add: leftTurn_def)

(*punkt A zwischen B und C*)
definition midpoint :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"midpoint a b c = (2 * getY a = getY b + getY c \<and> 2 * getX a = getX b + getX c)"
definition betwpoint :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"betwpoint a b c = (\<forall> n. n > 1 \<longrightarrow> (n * getY a = getY b + getY c \<and> n * getX a = getX b + getX c))"
lemma swapBetween [simp]: "betwpoint a c b = betwpoint a b c" by(auto simp add: betwpoint_def)

(*3 Punkte sind auf einer geraden*)
definition collinear :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"collinear a b c = ((getX a - getX b)*(getY b - getY c) = (getY a- getY b)*(getX b - getX c))"
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
lemma collRotate [simp]: "collinear c a b = collinear a b c"
  apply (simp add: collinear_def) apply algebra
done
lemma collSwap [simp]: "collinear a c b = collinear a b c"
  apply (simp add: collinear_def) apply algebra
done
lemma twoPointsColl [simp]: "collinear a b b" by (simp add: collinear_def)
lemma twoPointsColl2 [simp]: "collinear a a b" by (simp add: collinear_def)

(*move/translate point*)



(*Zusätliche lemmas*)
lemma notLeftTurn [simp]: "(\<not> leftTurn a c b) = (leftTurn a b c \<or> collinear a b c)"
  apply (simp add:leftTurn_def)
  apply (subst colliniearRight)
  apply (auto)
  apply (simp add: signedArea_def)
oops
lemma notBetweenSelf [simp]: "\<not> (betwpoint a a b)"
  apply (rule notI)
  apply (simp add: betwpoint_def)
  apply (cut_tac  r=a and p=b in pointsNotEqual)
  apply (erule_tac x = 2 in allE) apply (simp)
  apply (auto simp add: pointsEqual1)
oops
definition isBetween :: "[point2d, point2d, point2d] \<Rightarrow> bool" where
" isBetween b a c \<equiv> collinear a b c \<and> (\<exists> d. signedArea a c d \<noteq> 0) \<and>
(\<forall> d. signedArea a c d \<noteq> 0 \<longrightarrow>
0 < (signedArea a b d / signedArea a c d) \<and> (signedArea a b d / signedArea a c d) < 1 )"
lemma notBetweenSelf [simp]: "\<not> (isBetween a a b)"
  apply (rule notI)
  apply (simp add: isBetween_def)
  apply (auto simp add: pointsEqual1)
done
lemma notCollThenDiffPoints [intro]: "\<not>collinear a b c \<Longrightarrow> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"
  apply (simp add: collinear_def)
  apply (auto)
oops
lemma isBetweenPointsDistinct [intro]: "isBetween a b c \<Longrightarrow> a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c"
oops
lemma onePointIsBetween [intro]: "collinear a b c \<Longrightarrow>
isBetween a b c \<or> isBetween b a c \<or> isBetween c a b"
  apply (simp add: collinear_def)
oops
lemma areaContra [dest]: " signedArea a c b < 0\<Longrightarrow> signedArea a b c < 0  \<Longrightarrow> False"
  apply (simp add: signedArea_def)
oops
lemma areaContra2 [dest]: "0 < signedArea a c b\<Longrightarrow> 0 < signedArea a b c \<Longrightarrow> False"
oops
lemma notBetweenSamePoint [dest]: "betwpoint a b b \<Longrightarrow> False"
  apply (simp add: betwpoint_def)
  apply (erule_tac x = 2 in allE)
  apply (auto)
oops
lemma notBetween [dest]: "betwpoint A B C \<Longrightarrow>betwpoint B A C  \<Longrightarrow> False" oops
lemma notBetween2 [dest]: "betwpoint A B C \<Longrightarrow>betwpoint C A B  \<Longrightarrow> False" oops
lemma notBetween3 [dest]: "betwpoint B A C \<Longrightarrow>betwpoint C A B \<Longrightarrow> False" oops
lemma conflictingLeftTurns [dest]: "leftTurn a b c \<Longrightarrow> leftTurn a c b \<Longrightarrow> False"
  apply (simp add: leftTurn_def)            
oops
lemma conflictingLeftTurns2 [dest]: "leftTurn a b c \<Longrightarrow> betwpoint a b c \<Longrightarrow> False" oops
lemma conflictingLeftTurns3 [dest]: "leftTurn a b c \<Longrightarrow> collinear a b c \<Longrightarrow> False" oops
end
