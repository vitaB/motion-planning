theory polygon
imports cyclePath
begin

(*definition for polygon: intersectionfree cyclePath*)
definition polygon :: "point2d list \<Rightarrow> bool" where
  "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<equiv> intersectionFreePList P"
lemma notPolygon: "pointList [A,B,C] \<Longrightarrow> A isBetween C B \<Longrightarrow> polygon (cyclePath [A,B,C]) \<Longrightarrow> False"
  by(auto simp add: cyclePath_def polygon_def intersectionFreePList_def isBetweenImpliesCollinear)

(*List with polygons*)
definition polygonList :: "(point2d list) list \<Rightarrow> bool" where
  "pointLists PL \<Longrightarrow> polygonList PL \<equiv> \<forall> i < length PL. polygon (cyclePath (PL!i))"
(*jedes element ist ein polygon*)
lemma polygonListSimp[simp]: "pointLists PL \<Longrightarrow> i < length PL  \<Longrightarrow> polygonList PL \<Longrightarrow>
    polygon (cyclePath (PL!i))"
  by (simp add: polygonList_def)
lemma polygonListSimp1: "pointLists [A,B] \<Longrightarrow> (polygon (cyclePath A) \<and> polygon (cyclePath B))
    = polygonList [A,B]"
  apply (simp del: polygonListSimp add: polygonList_def, auto)
by (case_tac i, auto)
lemma polygonListSimp2 [simp]: "pointLists [A] \<Longrightarrow> polygon (cyclePath A) = polygonList [A]"
  by (auto simp add: polygonList_def)
  

(*(*count how many times a track intersects the polygon*)
fun countSegmentCrossPolygon :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> nat" where
  "countSegmentCrossPolygon [] S E = 0"
  | "countSegmentCrossPolygon [P] S E = 0"
  | "countSegmentCrossPolygon (Pf#Pl#Ps) S E = (if (crossing Pf Pl S E)
    then (1 + countSegmentCrossPolygon (Pl#Ps) S E)
    else(countSegmentCrossPolygon (Pl#Ps) S E))"

(*When is a point in a polygon?*)
definition pointInPolygon :: "point2d list \<Rightarrow> point2d \<Rightarrow> bool" where
  "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> pointInPolygon P A \<equiv>
    odd(countSegmentCrossPolygon P A (Abs_point2d(xCoord (last(xCoordSort P)) + 1, yCoord A)))" (*austauschen durch unendlich*)

(*polygon is partial or complete in another Polygon*)
definition polygonInPolygon :: "point2d list \<Rightarrow> point2d list \<Rightarrow> bool" where
  "pointList Lr\<Longrightarrow> Pr=cyclePath Lr\<Longrightarrow> polygon Pr\<Longrightarrow> pointList Lt\<Longrightarrow>Pt=cyclePath Lt \<Longrightarrow> polygon Pt\<Longrightarrow>
    polygonInPolygon Pr Pt \<equiv> (\<exists> i \<in> set Pr. pointInPolygon Pt i)
    \<or> (\<exists> j \<in> set Pt. pointInPolygon Pr j)"

lemma polygonInPolygonSym : "pointList Lr \<Longrightarrow> Pr = cyclePath Lr \<Longrightarrow> polygon Pr \<Longrightarrow> pointList Lt \<Longrightarrow>
  Pt = cyclePath Lt \<Longrightarrow> polygon Pt \<Longrightarrow> polygonInPolygon Pr Pt = polygonInPolygon Pt Pr"
  by (simp add: polygonInPolygon_def, rule iffI, blast+)
lemma polygonInPolygonSame: "pointList Lr \<Longrightarrow> Pr=cyclePath Lr \<Longrightarrow>polygon Pr \<Longrightarrow> 
  polygonInPolygon Pr Pr \<Longrightarrow> False"
  apply (auto simp add: polygonInPolygon_def pointInPolygon_def)
sorry

lemma polygonCrossing : "pointList Lr \<Longrightarrow> Pr = cyclePath Lr \<Longrightarrow> polygon Pr \<Longrightarrow> pointList Lt \<Longrightarrow>
    Pt = cyclePath Lt \<Longrightarrow> polygon Pt \<Longrightarrow> cyclePathIntersect Pr Pt \<Longrightarrow> \<not>polygonInPolygon Pr Pt"
sorry

definition polygonDisjoint :: "point2d list \<Rightarrow> point2d list \<Rightarrow> bool" where
  "pointList Ll\<Longrightarrow> P=cyclePath Ll\<Longrightarrow> polygon P \<Longrightarrow> pointList Lr\<Longrightarrow> R=cyclePath Lr \<Longrightarrow> polygon R \<Longrightarrow>
    polygonDisjoint P R \<equiv> \<not>polygonInPolygon P R \<and> \<not>cyclePathIntersect P R"(*point on Segment case*)
(*polygon ist zu sich selbst nicht disjoint*)
lemma polygonDisjointSame: "pointList Ll\<Longrightarrow> P=cyclePath Ll\<Longrightarrow> polygon P \<Longrightarrow> 
  polygonDisjoint P P \<Longrightarrow> False"
  apply (simp add: polygonDisjoint_def, safe)
using cyclePathIntersectSame by blast
lemma polygonDisjointSame1: "pointList Ll\<Longrightarrow> P=cyclePath Ll\<Longrightarrow> polygon P \<Longrightarrow> pointList Lr\<Longrightarrow>
    R=cyclePath Lr \<Longrightarrow> polygon R \<Longrightarrow> polygonDisjoint P R \<Longrightarrow> R \<noteq> P"
using polygonDisjointSame by blast
lemma polygonDisjointSym: "pointList Ll\<Longrightarrow> P=cyclePath Ll\<Longrightarrow> polygon P\<Longrightarrow> pointList Lr\<Longrightarrow> 
  R=cyclePath Lr\<Longrightarrow> polygon R \<Longrightarrow> polygonDisjoint P R = polygonDisjoint R P"
  apply (safe, simp add: polygonDisjoint_def)
  apply (simp add: cyclePathIntersect_def cyclePathSegments intersectSym1 lineCyclePathIntersEq
    polygonInPolygonSym)
by (simp add: cyclePathIntersect_def cyclePathSegments intersectSym1 lineCyclePathIntersEq
  polygonDisjoint_def polygonInPolygonSym)
  
definition polygonsDisjoint :: "(point2d list) list \<Rightarrow> bool" where
  "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> polygonsDisjoint PL \<equiv> \<forall> i j. (i\<noteq>j \<and>
    i < length PL \<and> j < length PL) \<longrightarrow>  polygonDisjoint (cyclePath (PL!i)) (cyclePath (PL!j))"

lemma polygonsDisjointSimp [simp]: "pointLists [A,B] \<Longrightarrow> polygonList [A,B] \<Longrightarrow>
  polygonDisjoint (cyclePath A) (cyclePath B) = polygonsDisjoint [A,B]" 
  apply (safe) defer apply (simp add: polygonsDisjoint_def)
  apply (erule_tac x=0 in allE, erule_tac x=1 in allE, simp)
  apply (simp add: polygonsDisjoint_def, (rule allI)+, safe)
  apply (case_tac "i=0", subgoal_tac "j=1", simp+, subgoal_tac "j=0", auto)
by (meson pointListsSimp polygonDisjointSym polygonListSimp1)
(*alle elemente sind disjoint, außer zu sich selbst*)
lemma polygonsDisjointSimp1: "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow>
  i < length PL \<Longrightarrow> j < length PL \<Longrightarrow> i \<noteq> j \<Longrightarrow> polygonsDisjoint PL \<Longrightarrow>
  polygonDisjoint (cyclePath (PL!i)) (cyclePath (PL!j))" 
by (auto simp add: polygonsDisjoint_def)
(*kein Polygon kommt doppet vor*)
lemma disjointPolygonListDistinct : "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> i < length PL \<Longrightarrow>
  j < length PL \<Longrightarrow> i \<noteq> j \<Longrightarrow> polygonsDisjoint PL \<Longrightarrow> distinct PL"
  apply (insert polygonDisjointSame1)
by(metis distinct_conv_nth pointListsSimp2 polygonListSimp polygonsDisjointSimp1)
  

(*disjointe polygonenListe, hat keine schnittpunkte*)
lemma polygonDisjoinPathsIntersect [simp]: "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow>
  polygonsDisjoint PL \<Longrightarrow> \<not>cyclePathsIntersect PL"
  apply (auto simp add: polygonsDisjoint_def cyclePathsIntersect_def)
  apply (erule_tac x=i in allE, erule_tac x=j in allE, simp add: polygonDisjoint_def)
by (cut_tac Ll="PL ! i" and P="cyclePath (PL ! i)" and Lr="PL ! j" and R="cyclePath (PL ! j)"
    in polygonDisjoint_def, simp+)
*)
  
  


(*convex Polygon:
- none of the edges of the polygon separates any of the remaining corners of the polygon
- 3 consecutive edges are not collinear*)
(*Note: in cyclepath there collinearität here. Namely, at the first edge + the last*)
definition cPolygon :: "point2d list \<Rightarrow> bool" where
"pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> cPolygon P \<equiv> (\<forall> k < length P - 1.
  \<not>(\<exists> i. i < length P - 1 \<and> lineSeparate (P ! k) (P ! Suc k) (P ! i) (P ! Suc i)))"

lemma cPolygonRevEq: "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> cPolygon (rev P) \<equiv>
  (\<forall> k < length (rev P) - 1.
  \<not>(\<exists> i. i < length (rev P) - 1 \<and> lineSeparate ((rev P) ! k) ((rev P) ! Suc k) ((rev P) ! i) ((rev P) ! Suc i)))"
  apply (cut_tac P="rev P" and L="hd L # rev (tl L)" in cPolygon_def, simp,simp add: cyclePath_def)
by (metis list.collapse list.size(3) not_less numeral_eq_Suc pointList_def
    rev.simps(2) zero_less_Suc, (simp)+)
lemma cPolygonRev: "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> cPolygon P \<Longrightarrow>
    cPolygon (rev P)"
  apply (simp add: cPolygonRevEq cPolygon_def, auto)
  apply (subgoal_tac "rev P = revCycle L")
  apply (simp add: cPolygon_def)
sorry

(*all triangles are conv. polygon*)
lemma conVextriangles: "pointList L \<Longrightarrow> length L = 3 \<Longrightarrow> \<not>collinearList L \<Longrightarrow>
  P = cyclePath L \<Longrightarrow> cPolygon P"
  apply (simp add:cPolygon_def cyclePath_def, safe)
  apply (simp add: lineSeparate_def, safe)
  apply (subgoal_tac "(k=0 \<and> i = 2) \<or> (k=1 \<and> i = 0) \<or> (k=2 \<and> i = 1)", safe)
    apply (auto simp add: rightTurn_def)
    apply (metis Nil_is_append_conv areaDoublePoint2 hd_append2 hd_conv_nth less_numeral_extra(3)
      list.size(3) nth_append_length signedAreaRotate)
    apply (metis add_2_eq_Suc' areaDoublePoint less_numeral_extra(3)
      monoid_add_class.add.left_neutral signedAreaRotate)
    apply (metis areaDoublePoint2 less_2_cases less_Suc_eq less_numeral_extra(3)
      numeral_eq_Suc pred_numeral_simps(3))
    apply (smt Nil_is_append_conv Suc_lessI areaDoublePoint hd_append2 hd_conv_nth signedAreaRotate
      length_greater_0_conv neq0_conv not_less_iff_gr_or_eq nth_append_length numeral_3_eq_3)
    apply (metis areaDoublePoint2 less_2_cases less_Suc_eq not_less_iff_gr_or_eq numeral_eq_Suc
      pred_numeral_simps(3))
    apply (smt Suc_1 Suc_eq_plus1_left areaDoublePoint2 less_2_cases less_Suc_eq
      less_numeral_extra(3) monoid_add_class.add.right_neutral numeral_3_eq_3)
    apply (metis colliniearRight less_2_cases less_Suc_eq less_numeral_extra(3)
      notCollThenDiffPoints numeral_eq_Suc pred_numeral_simps(3))
    apply (smt Nil_is_append_conv Suc_eq_plus1_left areaDoublePoint hd_append2 hd_conv_nth
      length_greater_0_conv less_Suc_eq less_nat_zero_code less_numeral_extra(3) nth_append_length
      numeral_3_eq_3 signedAreaRotate)
  apply (subgoal_tac "(k=0 \<and> i = 2) \<or> (k=1 \<and> i = 0) \<or> (k=2 \<and> i = 1)", auto)
    apply (metis Nil_is_append_conv areaDoublePoint2 hd_append2 hd_conv_nth less_numeral_extra(3)
      list.size(3) nth_append_length signedAreaRotate)
    apply (metis add_2_eq_Suc' areaDoublePoint less_numeral_extra(3)
      monoid_add_class.add.left_neutral)
    apply (metis areaDoublePoint2 less_2_cases less_Suc_eq less_numeral_extra(3)
      numeral_eq_Suc pred_numeral_simps(3))
    apply (smt Nil_is_append_conv Suc_lessI areaDoublePoint hd_append2 hd_conv_nth signedAreaRotate
      length_greater_0_conv neq0_conv not_less_iff_gr_or_eq nth_append_length numeral_3_eq_3)
    apply (metis areaDoublePoint2 less_2_cases less_Suc_eq not_less_iff_gr_or_eq numeral_eq_Suc
      pred_numeral_simps(3))
    apply (smt Suc_1 Suc_eq_plus1_left areaDoublePoint2 less_2_cases less_Suc_eq
      less_numeral_extra(3) monoid_add_class.add.right_neutral numeral_3_eq_3)
    apply (metis colliniearRight less_2_cases less_Suc_eq less_numeral_extra(3)
      notCollThenDiffPoints numeral_eq_Suc pred_numeral_simps(3))
    apply (smt Nil_is_append_conv Suc_eq_plus1_left areaDoublePoint hd_append2 hd_conv_nth
      length_greater_0_conv less_Suc_eq less_nat_zero_code less_numeral_extra(3) nth_append_length
      numeral_3_eq_3 signedAreaRotate)
done

(*in a conv. polygon none of the lines intersects*)
theorem cPolygonIsCrossingFree: "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow>
    cPolygon P \<Longrightarrow> crossingFreePList P"
  apply (simp add: crossingFreePList_def, safe, simp add: cPolygon_def)
  apply (erule_tac x=k in allE, simp, erule_tac x=i in allE, simp)
  apply (simp add: lineSeparate_def, safe, auto simp add: conflictingRigthTurns)
by(metis collRotate crossingCollinear crossingSym1 crossingRightTurn crossingSym rightTurnRotate2)+

(*in a conv. polygon none of the lines intersects(real)*)
theorem cPolygonIsIntersectionFree : "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow>
    cPolygon P \<Longrightarrow> intersectionFreePList P"
  apply (simp add: intersectionFreePList_def, safe)
  apply (cut_tac L=L and P=P and a="i" and b="Suc i" and c="k" in cyclePathNotCollinear)
    apply (simp add: cPolygon_def)+
    apply (cut_tac L=L and P=P and i=i in cyclePathSegments, (simp add: segment_def)+)
  apply (cut_tac L=L and P=P and a="i" and b="Suc i" and c="Suc k" in cyclePathNotCollinear)
    apply (simp add: cPolygon_def)+
    apply (cut_tac L=L and P=P and i=i in cyclePathSegments,
      (simp add: segment_def cyclePathAdjacentSame1)+)
  apply (cut_tac L=L and P=P and a="i" and b="Suc k" and c="k" in cyclePathNotCollinear)
    apply (simp add: cPolygon_def)+
    apply (cut_tac L=L and P=P and i=k in cyclePathSegments,
      (simp add: segment_def cyclePathAdjacentSame1)+)
  apply (cut_tac L=L and P=P and a="Suc i" and b="Suc k" and c="k" in cyclePathNotCollinear)
    apply (simp add: cPolygon_def)+
    apply (cut_tac L=L and P=P and i=k in cyclePathSegments, (simp add: segment_def cyclePathAdjacentSame1)+)
  apply (simp add: cPolygon_def, erule_tac x=k in allE, simp, erule_tac x=i in allE, simp)
  apply (simp add: lineSeparate_def, safe, metis conflictingRigthTurns)
  apply (cut_tac A="cyclePath L ! i" and B="cyclePath L ! Suc i" and P="cyclePath L ! k" and R="cyclePath L ! Suc k" in intersectSym1)
    using segment_def apply auto[1]
  apply ((simp add: cyclePathSegments conflictingRigthTurns1))
  apply (metis Suc_eq_plus1 Suc_mono cyclePathSegments cyclePath_def intersectRightTurn
    length_append_singleton less_diff_conv rightTurnRotate2)
  apply (cut_tac A="cyclePath L ! i" and B="cyclePath L ! Suc i" and P="cyclePath L ! k" and R="cyclePath L ! Suc k" in intersectRightTurn1)
    apply ((simp add: cyclePathSegments conflictingRigthTurns1)+, blast)
by (simp add: colliniearRight cyclePathNotCollinear1 numeral_2_eq_2 pointList_def)

(*each conv. polygon is also a simple polygon*)
lemma cPolygonIsPolygon : "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow>
    cPolygon P \<Longrightarrow> polygon P"
  by (simp add: polygon_def cPolygonIsIntersectionFree)


(*(*Punkt inside convex Polygon.*)
(*Testweise. überprüfe ob Punkt für alle segmente des Polygons rechts oder links gerichtet ist*)
(*wenn Punkt auf Kante liegt, zählt es nicht.*)
definition pointInsideCPolygonACl :: "point2d list \<Rightarrow> point2d \<Rightarrow> bool" where
"pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> cPolygon P \<Longrightarrow>
  pointInsideCPolygonACl P a \<equiv> \<forall> i j. 0 \<le> i \<and> j = i + 1 \<and> j < size P \<longrightarrow> signedArea (P!i) (P!j) a > 0"
definition pointInsideCPolygonCCl :: "point2d list \<Rightarrow> point2d \<Rightarrow> bool" where
"pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> cPolygon P \<Longrightarrow>
  pointInsideCPolygonCCl P a \<equiv> pointInsideCPolygonACl (rev P) a"
(*irgndwo hier ist ein Denkfehler*)
theorem pointInsideCPolygonCClEq : "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> cPolygon P \<Longrightarrow> \<not>collinearList L \<Longrightarrow>
  pointInsideCPolygonCCl P a = (\<forall> i j. 0 \<le> i \<and> j = i + 1 \<and> j < size P \<longrightarrow> signedArea (P!i) (P!j) a < 0)"
  apply (simp only: pointInsideCPolygonCCl_def)
  apply (cut_tac P="rev P" and a=a and L="hd L # rev (tl L)" in pointInsideCPolygonACl_def, simp)
    apply (metis revCycleEq revCycle_def)
    apply (simp add: cPolygonRev) 
  apply (simp, rule iffI, safe)
  apply (thin_tac "pointInsideCPolygonACl (rev (cyclePath L)) a \<equiv>
         \<forall>i<length L. 0 < signedArea a (rev (cyclePath L) ! i) (rev (cyclePath L) ! Suc i)")
  apply (erule_tac x="(length (cyclePath L) - 1) - i" in allE)
  apply (erule impE)
  apply (simp add: cyclePath_def)
sorry

definition pointInsideCPolygon :: "point2d list \<Rightarrow> point2d \<Rightarrow> bool" where
  "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> cPolygon P \<Longrightarrow>
  pointInsideCPolygon P a \<equiv> pointInsideCPolygonCCl P a \<or> pointInsideCPolygonACl P a"
lemma pointInsideCPolygonRev1: "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> cPolygon P \<Longrightarrow>
  pointInsideCPolygon (rev P) a \<equiv> pointInsideCPolygonCCl (rev P) a \<or> pointInsideCPolygonACl (rev P) a"
  apply (cut_tac P=P and L=L in cPolygonRev, assumption+)
  apply (cut_tac P="rev P" and L="hd L # rev (tl L)" and a=a in pointInsideCPolygon_def)
  apply (simp, simp add: cyclePath_def)
  apply (metis list.collapse list.size(3) not_less numeral_eq_Suc pointList_def rev.simps(2) zero_less_Suc)
  apply (simp)
by auto
theorem pointInsideCPolygonRev: "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> cPolygon P \<Longrightarrow>
  pointInsideCPolygon P a = pointInsideCPolygon (rev P) a"
  apply (cut_tac P=P and L=L in cPolygonRev, assumption+)
  apply (simp add: pointInsideCPolygonRev1 pointInsideCPolygon_def, safe)
  apply (auto simp add: pointInsideCPolygonCCl_def)
sorry

lemma "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> cPolygon P \<Longrightarrow>
  pointInsideCPolygon P a \<Longrightarrow> pointInPolygon P a" thm cPolygonIsPolygon
  apply (cut_tac L=L and P=P in cPolygonIsPolygon, assumption+)
oops

(*Segment inside convex Polygon. Testweise*)
definition segmentInsideCPolygon :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "segment A B \<Longrightarrow> pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> cPolygon P \<Longrightarrow>
  segmentInsideCPolygon P A B \<equiv> pointInsideCPolygon P A \<and> pointInsideCPolygon P B" 

(*wenn ein punkt einer Strecke inside convex Polygon und ein Punkt einer Strecke outside, dann gibt es eine intersection*)
lemma twoPointPolygonInter : "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow>  \<not>collinearList L \<Longrightarrow> cPolygon P
  \<Longrightarrow> pointInsideCPolygon P a \<Longrightarrow> \<not>pointInsideCPolygon P b \<Longrightarrow> lineCyclePathInters P a b"
  apply (subgoal_tac "segment a b")
    apply (subst lineCyclePathIntersEq, simp)
    apply (simp add: pointInsideCPolygon_def pointInsideCPolygonACl_def)
    apply (simp add: pointInsideCPolygonCClEq, safe)
    apply (erule_tac x="ia" in allE, simp)
    apply (rule_tac x="ia" in exI, simp)
    apply (subgoal_tac "segment (cyclePath L ! ia) (cyclePath L ! Suc ia)")
sorry
(*wenn segment inside convex Polygon, dann schneidet das segment das Polygon nicht*)
lemma "segment A B \<Longrightarrow> pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> cPolygon P \<Longrightarrow>
  segmentInsideCPolygon P A B \<Longrightarrow> \<not>lineCyclePathInters P A B"
oops*)




(*alte Definition*)
end
