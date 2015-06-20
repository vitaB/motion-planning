theory polygon
imports cyclePath
begin

(*Convexes Polygon.
- keiner der Kanten des Polygons trennt irgendeine der übrigen Ecken einer der Kanten des Polygons
- 3 aufeainder folgenden Kanten sind nicht kollinear*)
definition polygon :: "point2d list \<Rightarrow> bool" where
"pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<equiv> \<not>collinearPointInList P \<and> (\<forall> k < length P - 1.
  \<not>(\<exists> i. i < length P - 1 \<and> lineSeparate (P ! k) (P ! Suc k) (P ! i) (P ! Suc i)))"

(*alle Dreiecke sind Polygone*)
lemma "pointList L \<Longrightarrow> length L = 3 \<Longrightarrow> \<not>collinearPointInList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P"
sorry (*Beweis unten*)
  (*apply (simp add:polygon_def cyclePath_def, safe)
  apply (cases L rule: collinearPointInList.cases, auto)
  apply (cases L rule: collinearPointInList.cases, auto)
  apply (simp add: lineSeparate_def, safe)
  apply (subgoal_tac "(k=0 \<and> i = 2) \<or> (k=1 \<and> i = 0) \<or> (k=2 \<and> i = 1)", safe)
  apply (auto)
  apply (smt2 Suc_leI Suc_lessI areaDoublePoint2 less_numeral_extra(3) neq0_conv not_less nth_Cons' nth_Cons_Suc numeral_3_eq_3)
  apply (metis One_nat_def Suc_leI Suc_lessI colliniearRight diff_Suc_1 less_numeral_extra(3) neq0_conv notCollThenDiffPoints not_less nth_Cons_0 nth_Cons_Suc numeral_3_eq_3)
  apply (metis Suc_eq_plus1_left Suc_leI add_diff_cancel_left' colliniearRight gr0_conv_Suc monoid_add_class.add.right_neutral notCollThenDiffPoints not_less not_less_iff_gr_or_eq nth_Cons_Suc numeral_3_eq_3)  
  apply (smt2 One_nat_def Suc_1 Suc_leI areaDoublePoint2 less_2_cases not_less not_less_iff_gr_or_eq nth_Cons_Suc numeral_3_eq_3 signedAreaRotate)
  apply (smt2 One_nat_def Suc_1 Suc_leI areaDoublePoint2 diff_Suc_1 less_2_cases not_less not_less_iff_gr_or_eq nth_Cons' numeral_3_eq_3 signedAreaRotate)
  apply (smt2 One_nat_def Suc_1 Suc_lessI Suc_less_eq areaDoublePoint less_2_cases less_numeral_extra(3) not_less nth_Cons' nth_Cons_Suc numeral_3_eq_3 signedAreaRotate)
  apply (subgoal_tac "(k=0 \<and> i = 2) \<or> (k=1 \<and> i = 0) \<or> (k=2 \<and> i = 1)", safe)
  apply (auto)
  apply (smt2 Suc_leI Suc_lessI areaDoublePoint2 less_numeral_extra(3) neq0_conv not_less nth_Cons' nth_Cons_Suc numeral_3_eq_3)
  apply (metis One_nat_def Suc_leI Suc_lessI colliniearRight diff_Suc_1 less_numeral_extra(3) neq0_conv notCollThenDiffPoints not_less nth_Cons_0 nth_Cons_Suc numeral_3_eq_3)
  apply (metis Suc_eq_plus1_left Suc_leI add_diff_cancel_left' colliniearRight gr0_conv_Suc monoid_add_class.add.right_neutral notCollThenDiffPoints not_less not_less_iff_gr_or_eq nth_Cons_Suc numeral_3_eq_3)  
  apply (smt2 One_nat_def Suc_1 Suc_leI areaDoublePoint2 less_2_cases not_less not_less_iff_gr_or_eq nth_Cons_Suc numeral_3_eq_3 signedAreaRotate)
  apply (smt2 One_nat_def Suc_1 Suc_leI areaDoublePoint2 diff_Suc_1 less_2_cases not_less not_less_iff_gr_or_eq nth_Cons' numeral_3_eq_3 signedAreaRotate)
  apply (smt2 One_nat_def Suc_1 Suc_lessI Suc_less_eq areaDoublePoint less_2_cases less_numeral_extra(3) not_less nth_Cons' nth_Cons_Suc numeral_3_eq_3 signedAreaRotate)
done*)

(*keine 3 aufeinander folgenden Punkte im Polygon sind collinear*)
lemma "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow>(\<forall> a < length P - 2. signedArea (P ! a) (P ! Suc a) (P ! Suc (Suc a)) \<noteq> 0)"
  apply (rule allI)
  apply (simp add: polygon_def collinearPointInListEq)
by (simp add: colliniearRight)
(*keine 3 Punkte im Polygon sind collinear*)
lemma "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> a \<noteq> b \<and> a \<noteq> c \<and> c \<noteq> b \<Longrightarrow>  \<not> collinear (P ! a) (P ! b) (P ! c)"
  apply (simp add: polygon_def)
  apply (erule_tac x=a in allE)
oops
(*alle 3 aufeinander folgenden Punkte im Polygon sind links oder rechts gerichtet*)
lemma "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> (\<forall> a < length P - 2. signedArea (P ! a) (P ! Suc a) (P ! Suc (Suc a)) < 0)
  \<or> (\<forall> a < length P - 2. signedArea (P ! a) (P ! Suc a) (P ! Suc (Suc a)) > 0)"
  (*apply (simp add: polygon_def lineSeparate_def)
  apply (auto)
  apply (rule disjI1)*)
oops

(*in einem polygon kreuzt sich keiner der Strecken*)
lemma "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> intersectionFreePList P"
  apply (auto simp add: polygon_def intersectionFreePList_def)
  apply (erule_tac x=i in allE, erule impE, assumption)
  apply (erule_tac x=k in allE)
  apply (simp add: lineSeparate_def)
sorry



(*intersection(Polygon, Polygon)*)



(*Punkt inside convex Polygon. Testweise*)
definition insidePolygonACl :: "point2d list \<Rightarrow> point2d \<Rightarrow> bool" where
"pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> insidePolygonACl P a \<equiv> \<forall> i j. 0 \<le> i \<and> j = i + 1 \<and> j < size P \<longrightarrow> signedArea (P!i) (P!j) a > 0"


(*wenn ein punkt einer Strecke inside Polygon und ein Punkt einer Strecke outside, dann gibt es eine intersection*)


(*Punkt outside Polygon*)


(*move Polygon*)


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
