theory simpTrapezoidal
imports polygon "~~/src/HOL/Hoare/Hoare_Logic"
begin

(*4eckige Box um pointListe herum ist selbst eine pointList*)
lemma rBoxPointList: "pointList L \<Longrightarrow> 
  pointList ([\<lparr>xCoord = hd (xCoordList L) - 1, yCoord = hd (yCoordList L) - 1\<rparr> ,\<lparr>xCoord = last (xCoordList L) + 1, yCoord = hd (yCoordList L) - 1\<rparr>,
  \<lparr>xCoord = last (xCoordList L) + 1, yCoord = last (yCoordList L) + 1\<rparr>,\<lparr>xCoord = hd (xCoordList L) - 1, yCoord = last (yCoordList L) + 1\<rparr>])"
  apply (cut_tac P=L in YCoordSorted)
  apply (cut_tac P=L in XCoordSorted)
  apply (cases L rule: xCoordList.cases)
  apply (subst (asm) pointList_def, simp)
  apply (simp only: xCoordList.simps)
  apply (simp only: pointList_def)
  apply (rule conjI)
  apply (simp add: pointList_def)
  (*apply (subgoal_tac "x \<notin> set xs")
  apply (auto)*)
sorry

(*4eckige Box um pointListe herum*)
definition rBox :: "point2d list \<Rightarrow> point2d list" where
"pointList L \<Longrightarrow> rBox L \<equiv> polygon([\<lparr>xCoord = hd (xCoordList L) - 1, yCoord = hd (yCoordList L) - 1\<rparr>
 ,\<lparr>xCoord = last (xCoordList L) + 1, yCoord = hd (yCoordList L) - 1\<rparr>, \<lparr>xCoord = last (xCoordList L) + 1, yCoord = last (yCoordList L) + 1\<rparr>,
\<lparr>xCoord = hd (xCoordList L) - 1, yCoord = last (yCoordList L) + 1\<rparr>])"

(*ersetzte den Term Polygon im Satz. Funktioniert noch nicht!*)
lemma rBoxPoly : "pointList L \<Longrightarrow>
  (polygon([\<lparr>xCoord = hd (xCoordList L) - 1, yCoord = hd (yCoordList L) - 1\<rparr>,\<lparr>xCoord = last (xCoordList L) + 1, yCoord = hd (yCoordList L) - 1\<rparr>,
  \<lparr>xCoord = last (xCoordList L) + 1, yCoord = last (yCoordList L) + 1\<rparr>,\<lparr>xCoord = hd (xCoordList L) - 1, yCoord = last (yCoordList L) + 1\<rparr>]))
  = [\<lparr>xCoord = hd (xCoordList L) - 1, yCoord = hd (yCoordList L) - 1\<rparr> ,\<lparr>xCoord = last (xCoordList L) + 1, yCoord = hd (yCoordList L) - 1\<rparr>,
  \<lparr>xCoord = last (xCoordList L) + 1, yCoord = last (yCoordList L) + 1\<rparr>, \<lparr>xCoord = hd (xCoordList L) - 1, yCoord = last (yCoordList L) + 1\<rparr>,
  \<lparr>xCoord = hd (xCoordList L) - 1, yCoord = hd (yCoordList L) - 1\<rparr>]"
  apply (cut_tac L=L in rBoxPointList, assumption)
  apply (auto simp add: rBox_def polygon_def)
done

(*rBox ist ein Convexes Polygon*)
lemma rBoxConvex : "pointList L \<Longrightarrow> conv_polygon (rBox L)"
  apply (cut_tac L=L in rBoxPointList, assumption)
  apply (simp add: rBox_def)
  apply (simp add: conv_polygon_def)  
  apply (rule disjI2)
  apply (subst rBoxPoly, assumption)
  apply (auto simp add: signedArea_def)
  apply (subgoal_tac "last (xCoordList L) - hd (xCoordList L) \<ge> 0")
  apply (subgoal_tac "last (yCoordList L) - hd (yCoordList L) \<ge> 0", simp)
  apply (auto simp add: yCoordOrd1 le_diff_eq xCoordOrd1)
  apply (subgoal_tac "last (xCoordList L) - hd (xCoordList L) \<ge> 0")
  apply (subgoal_tac "hd (yCoordList L) - last (yCoordList L) \<le> 0")
  apply (simp add: mult_less_0_iff)
  apply (auto simp add: yCoordOrd1 le_diff_eq xCoordOrd1)
  apply (subgoal_tac "last (xCoordList L) - hd (xCoordList L) \<ge> 0")
  apply (subgoal_tac "last (yCoordList L) - hd (yCoordList L) \<ge> 0", simp)
  apply (auto simp add: le_diff_eq yCoordOrd1 xCoordOrd1)
done
  
(*alle Punkte von L sind innerhalb von rBox L*)
lemma "pointList L \<Longrightarrow> VARS (xs :: point2d list) i {pointList L}
  xs := [];
  i := 0;
  WHILE i \<noteq> length L
  INV {\<forall> j. 0 \<le> j \<and> j \<le> i  \<longrightarrow> insidePolygonACl (rBox L) (L!i)}
  DO
    i := i + 1
  OD
  {\<forall> j. 0 \<le> j \<and> j \<le> i  \<longrightarrow> insidePolygonACl (rBox L) (L!i)}"
  apply(vcg_simp, auto)
  apply (cut_tac L=L in rBoxConvex, assumption)
  apply (simp add: insidePolygonACl_def)
  apply (simp add: rBox_def)
  apply (cut_tac L=L in  rBoxPoly, assumption)
  apply (simp)
oops

(*Welche TrapezStrecken schneiden das Segment*)
(*ich brauche doch ein segment-datentypen?*)
fun trapezInter :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> real list" where
  "trapezInter [] A B = []"
 | " trapezInter [p] A B = []"
  | "trapezInter (p#r#xs) A B = (if (segment A B \<and> intersect A B p r) then (getX p # trapezInter xs A B) else trapezInter xs A B)"

(*S = Menge von Strecken. keine gleiche x-Koordinate. Strecken Kreuzugsfrei*)
(*fun trapezoidalMap ::  "point2d list \<Rightarrow> real list" where
"trapezoidalMap [] = []"
| "trapezoidalMap (x#xs) = insort_insert (getX x) (trapezoidalMap xs)"*)


end
