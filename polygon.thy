theory polygon
imports cyclePath
begin

(*Convexes Polygon.
- keiner der Kanten des Polygons trennt irgendeine der übrigen Ecken einer der Kanten des Polygons
- 3 aufeainder folgenden Kanten sind nicht kollinear*)
(*Bemerkung: im cyclePath gibt es hier collinearität. Und zwar an der letzten+ersten Kante*)
definition polygon :: "point2d list \<Rightarrow> bool" where
"pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> polygon P \<equiv> (\<forall> k < length P - 1.
  \<not>(\<exists> i. i < length P - 1 \<and> lineSeparate (P ! k) (P ! Suc k) (P ! i) (P ! Suc i)))"

lemma polygonRevEq: "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> polygon (rev P) \<equiv>
  (\<forall> k < length (rev P) - 1.
  \<not>(\<exists> i. i < length (rev P) - 1 \<and> lineSeparate ((rev P) ! k) ((rev P) ! Suc k) ((rev P) ! i) ((rev P) ! Suc i)))"
  apply (cut_tac P="rev P" and L="hd L # rev (tl L)" in polygon_def)
  apply (simp, simp add: cyclePath_def)
  apply (metis list.collapse list.size(3) not_less numeral_eq_Suc pointList_def rev.simps(2) zero_less_Suc)
  apply (simp)+
done
lemma polygonRev: "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> polygon P \<Longrightarrow> polygon (rev P)"
  apply (simp add: polygonRevEq polygon_def, auto)
  apply (subgoal_tac "rev P = revCycle L")
  apply (simp add: polygon_def)
sorry

(*alle Dreiecke sind conv. Polygone*)
lemma "pointList L \<Longrightarrow> length L = 3 \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P"
 (*Beweis braucht zu lange: apply (simp add:polygon_def cyclePath_def, safe)
  apply (simp add: lineSeparate_def, safe)
  apply (subgoal_tac "(k=0 \<and> i = 2) \<or> (k=1 \<and> i = 0) \<or> (k=2 \<and> i = 1)", safe)
    apply (auto simp add: rightTurn_def)
    apply (metis Nil_is_append_conv areaDoublePoint2 hd_append2 hd_conv_nth less_numeral_extra(3) list.size(3) nth_append_length signedAreaRotate)
    apply (metis add_2_eq_Suc' areaDoublePoint less_numeral_extra(3) monoid_add_class.add.left_neutral signedAreaRotate)
    apply (metis areaDoublePoint2 less_2_cases less_Suc_eq less_numeral_extra(3) numeral_eq_Suc pred_numeral_simps(3))
    apply (smt2 Nil_is_append_conv Suc_lessI areaDoublePoint hd_append2 hd_conv_nth length_greater_0_conv neq0_conv not_less_iff_gr_or_eq nth_append_length numeral_3_eq_3 signedAreaRotate)
    apply (metis areaDoublePoint2 less_2_cases less_Suc_eq not_less_iff_gr_or_eq numeral_eq_Suc pred_numeral_simps(3))
    apply (smt2 Suc_1 Suc_eq_plus1_left areaDoublePoint2 less_2_cases less_Suc_eq less_numeral_extra(3) monoid_add_class.add.right_neutral numeral_3_eq_3)
    apply (metis colliniearRight less_2_cases less_Suc_eq less_numeral_extra(3) notCollThenDiffPoints numeral_eq_Suc pred_numeral_simps(3))
    apply (smt2 Nil_is_append_conv Suc_eq_plus1_left areaDoublePoint hd_append2 hd_conv_nth length_greater_0_conv less_Suc_eq less_nat_zero_code less_numeral_extra(3) nth_append_length numeral_3_eq_3 signedAreaRotate)
  apply (subgoal_tac "(k=0 \<and> i = 2) \<or> (k=1 \<and> i = 0) \<or> (k=2 \<and> i = 1)", auto)
    apply (metis Nil_is_append_conv areaDoublePoint2 hd_append2 hd_conv_nth less_numeral_extra(3) list.size(3) nth_append_length signedAreaRotate)
    apply (metis add_2_eq_Suc' areaDoublePoint less_numeral_extra(3) monoid_add_class.add.left_neutral)
    apply (metis areaDoublePoint2 less_2_cases less_Suc_eq less_numeral_extra(3) numeral_eq_Suc pred_numeral_simps(3))
    apply (smt2 Nil_is_append_conv Suc_lessI areaDoublePoint hd_append2 hd_conv_nth length_greater_0_conv neq0_conv not_less_iff_gr_or_eq nth_append_length numeral_3_eq_3 signedAreaRotate)
    apply (metis areaDoublePoint2 less_2_cases less_Suc_eq not_less_iff_gr_or_eq numeral_eq_Suc pred_numeral_simps(3))
    apply (smt2 Suc_1 Suc_eq_plus1_left areaDoublePoint2 less_2_cases less_Suc_eq less_numeral_extra(3) monoid_add_class.add.right_neutral numeral_3_eq_3)
    apply (metis colliniearRight less_2_cases less_Suc_eq less_numeral_extra(3) notCollThenDiffPoints numeral_eq_Suc pred_numeral_simps(3))
    apply (smt2 Nil_is_append_conv Suc_eq_plus1_left areaDoublePoint hd_append2 hd_conv_nth length_greater_0_conv less_Suc_eq less_nat_zero_code less_numeral_extra(3) nth_append_length numeral_3_eq_3 signedAreaRotate)
done*)sorry

(*in einem conv. polygon kreuzt sich keiner der Strecken*)
theorem "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> crossingFreePList P"
  apply (simp add: crossingFreePList_def, safe)
  apply (simp add: polygon_def)
  apply (erule_tac x=k in allE, simp, erule_tac x=i in allE, simp)
  apply (simp add: lineSeparate_def, safe)
  apply (auto simp add: conflictingRigthTurns)
  apply (metis collRotate crossingCollinear crossingSym1 crossingRightTurn crossingSym rightTurnRotate2)+
done

(*in einem conv. polygon überschneidet sich keiner der Strecken*)
theorem "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> intersectionFreePList P"
  apply (simp add: intersectionFreePList_def, safe)
  apply (cut_tac L=L and P=P and a="i" and b="Suc i" and c="k" in cyclePathNotCollinear)
    apply (simp add: polygon_def)+
    apply (cut_tac L=L and P=P and i=i in cyclePathSegments, (simp add: segment_def)+)
  apply (cut_tac L=L and P=P and a="i" and b="Suc i" and c="Suc k" in cyclePathNotCollinear)
    apply (simp add: polygon_def)+
    apply (cut_tac L=L and P=P and i=i in cyclePathSegments, (simp add: segment_def cyclePathAdjacentSame1)+)
  apply (cut_tac L=L and P=P and a="i" and b="Suc k" and c="k" in cyclePathNotCollinear)
    apply (simp add: polygon_def)+
    apply (cut_tac L=L and P=P and i=k in cyclePathSegments, (simp add: segment_def cyclePathAdjacentSame1)+)
  apply (cut_tac L=L and P=P and a="Suc i" and b="Suc k" and c="k" in cyclePathNotCollinear)
    apply (simp add: polygon_def)+
    apply (cut_tac L=L and P=P and i=k in cyclePathSegments, (simp add: segment_def cyclePathAdjacentSame1)+)
  apply (simp add: polygon_def)
  apply (erule_tac x=k in allE, simp, erule_tac x=i in allE, simp)
  apply (simp add: lineSeparate_def, safe)
  apply (metis conflictingRigthTurns)
  apply (cut_tac A="cyclePath L ! i" and B="cyclePath L ! Suc i" and P="cyclePath L ! k" and R="cyclePath L ! Suc k" in intersectSym1)
    apply (simp)
    apply (cut_tac A="(cyclePath L ! k)" and B="(cyclePath L ! Suc k)" and P="(cyclePath L ! i)" and R="(cyclePath L ! Suc i)" in intersectRightTurn)
  apply ((simp add: cyclePathSegments conflictingRigthTurns1)+)
  apply (cut_tac A="cyclePath L ! i" and B="cyclePath L ! Suc i" and P="cyclePath L ! k" and R="cyclePath L ! Suc k" in intersectRightTurn1)
    apply ((simp add: cyclePathSegments conflictingRigthTurns1)+)
by (metis conflictingRigthTurns1 rightTurnRotate2)


(*Punkt inside convex Polygon.*)
(*Testweise. überprüfe ob Punkt für alle segmente des Polygons rechts oder links gerichtet ist*)
(*wenn Punkt auf Kante liegt, zählt es nicht.*)
definition pointInsidePolygonACl :: "point2d list \<Rightarrow> point2d \<Rightarrow> bool" where
"pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow>
  pointInsidePolygonACl P a \<equiv> \<forall> i j. 0 \<le> i \<and> j = i + 1 \<and> j < size P \<longrightarrow> signedArea (P!i) (P!j) a > 0"
definition pointInsidePolygonCCl :: "point2d list \<Rightarrow> point2d \<Rightarrow> bool" where
"pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow>
  pointInsidePolygonCCl P a \<equiv> pointInsidePolygonACl (rev P) a"
(*irgndwo hier ist ein Denkfehler*)
theorem pointInsidePolygonCClEq : "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> \<not>collinearList L \<Longrightarrow>
  pointInsidePolygonCCl P a = (\<forall> i j. 0 \<le> i \<and> j = i + 1 \<and> j < size P \<longrightarrow> signedArea (P!i) (P!j) a < 0)"
  apply (simp only: pointInsidePolygonCCl_def)
  apply (cut_tac P="rev P" and a=a and L="hd L # rev (tl L)" in pointInsidePolygonACl_def, simp)
    apply (metis revCycleEq revCycle_def)
    apply (simp add: polygonRev) 
  apply (simp, rule iffI, safe)
  apply (thin_tac "pointInsidePolygonACl (rev (cyclePath L)) a \<equiv>
         \<forall>i<length L. 0 < signedArea a (rev (cyclePath L) ! i) (rev (cyclePath L) ! Suc i)")
  apply (erule_tac x="(length (cyclePath L) - 1) - i" in allE)
  apply (erule impE)
  apply (simp add: cyclePath_def)
sorry

definition pointInsidePolygon :: "point2d list \<Rightarrow> point2d \<Rightarrow> bool" where
  "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow>
  pointInsidePolygon P a \<equiv> pointInsidePolygonCCl P a \<or> pointInsidePolygonACl P a"
lemma pointInsidePolygonRev1: "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> polygon P \<Longrightarrow>
  pointInsidePolygon (rev P) a \<equiv> pointInsidePolygonCCl (rev P) a \<or> pointInsidePolygonACl (rev P) a"
  apply (cut_tac P=P and L=L in polygonRev, assumption+)
  apply (cut_tac P="rev P" and L="hd L # rev (tl L)" and a=a in pointInsidePolygon_def)
  apply (simp, simp add: cyclePath_def)
  apply (metis list.collapse list.size(3) not_less numeral_eq_Suc pointList_def rev.simps(2) zero_less_Suc)
  apply (simp)
by auto
theorem pointInsidePolygonRev: "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> polygon P \<Longrightarrow>
  pointInsidePolygon P a = pointInsidePolygon (rev P) a"
  apply (cut_tac P=P and L=L in polygonRev, assumption+)
  apply (simp add: pointInsidePolygonRev1 pointInsidePolygon_def, safe)
  apply (auto simp add: pointInsidePolygonCCl_def)
sorry

(*Segment inside convex Polygon. Testweise*)
definition segmentInsidePolygon :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "segment A B \<Longrightarrow> pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow>
  segmentInsidePolygon P A B \<equiv> pointInsidePolygon P A \<and> pointInsidePolygon P B" 

(*wenn ein punkt einer Strecke inside Polygon und ein Punkt einer Strecke outside, dann gibt es eine intersection*)
lemma twoPointPolygonInter : "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow>  \<not>collinearList L \<Longrightarrow> polygon P \<Longrightarrow> pointInsidePolygon P a \<Longrightarrow>
  \<not>pointInsidePolygon P b \<Longrightarrow> lineCyclePathInters P a b"
  apply (subgoal_tac "segment a b")
    apply (subst lineCyclePathIntersEq, simp)
    apply (simp add: pointInsidePolygon_def pointInsidePolygonACl_def)
    apply (simp add: pointInsidePolygonCClEq, safe)
    apply (erule_tac x="ia" in allE, simp)
    apply (rule_tac x="ia" in exI, simp)
    apply (subgoal_tac "segment (cyclePath L ! ia) (cyclePath L ! Suc ia)")   
sorry
(*wenn segment inside convex Polygon, dann schneidet das segment das Polygon nicht*)
lemma "segment A B \<Longrightarrow> pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> polygon P \<Longrightarrow>
  segmentInsidePolygon P A B \<Longrightarrow> \<not>lineCyclePathInters P A B"
oops



(*alte Definition
(*conv. Polygone die im Uhrzeigersinn gespeichert werden, werden damit nicht erkannt!*)
fun pointsACl :: "point2d list \<Rightarrow> bool" where 
  "pointsACl [] = True"
|  "pointsACl [a] = True"
|  "pointsACl [a,b] = True"
|  "pointsACl (a#b#c#xs) = (signedArea a b c > 0 \<and> pointsACl (b#c#xs))"
definition pointsCl :: "point2d list \<Rightarrow> bool" where 
  "pointsCl P \<equiv> pointsACl (rev P)"
*)
end
