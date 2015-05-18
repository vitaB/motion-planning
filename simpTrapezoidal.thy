theory simpTrapezoidal
imports polygon
begin

(*4eckige Box um pointListe herum ist selbst eine pointList*)
lemma rBoxPointList: "pointList L \<Longrightarrow> let dist = 1 in
  pointList ([\<lparr>xCoord = hd (xCoordList L) - dist, yCoord = hd (yCoordList L) - dist\<rparr> ,\<lparr>xCoord = last (xCoordList L) + dist, yCoord = hd (yCoordList L) - dist\<rparr>,
  \<lparr>xCoord = last (xCoordList L) + dist, yCoord = last (yCoordList L) + dist\<rparr>,\<lparr>xCoord = hd (xCoordList L) - dist, yCoord = last (yCoordList L) + dist\<rparr>])"
  apply (subst pointList_def, auto)
  apply (simp add: pointList_def)
  apply (induction L rule: xCoordList.induct)
  apply (simp, simp)
sorry
(*4eckige Box um pointListe herum*)
definition rBox :: "point2d list \<Rightarrow> point2d list" where
"pointList L \<Longrightarrow> rBox L \<equiv> let dist = 1 in polygon([\<lparr>xCoord = hd (xCoordList L) - dist, yCoord = hd (yCoordList L) - dist\<rparr>
 ,\<lparr>xCoord = last (xCoordList L) + dist, yCoord = hd (yCoordList L) - dist\<rparr>, \<lparr>xCoord = last (xCoordList L) + dist, yCoord = last (yCoordList L) + dist\<rparr>,
\<lparr>xCoord = hd (xCoordList L) - dist, yCoord = last (yCoordList L) + dist\<rparr>])"
(*ersetzte den Term Polygon im Satz. Funktioniert noch nicht!*)
lemma rBox1 : "pointList L \<Longrightarrow> let dist = 1 in
  (polygon([\<lparr>xCoord = hd (xCoordList L) - dist, yCoord = hd (yCoordList L) - dist\<rparr>,\<lparr>xCoord = last (xCoordList L) + dist, yCoord = hd (yCoordList L) - dist\<rparr>,
  \<lparr>xCoord = last (xCoordList L) + dist, yCoord = last (yCoordList L) + dist\<rparr>,\<lparr>xCoord = hd (xCoordList L) - dist, yCoord = last (yCoordList L) + dist\<rparr>]))
  = [\<lparr>xCoord = hd (xCoordList L) - dist, yCoord = hd (yCoordList L) - dist\<rparr> ,\<lparr>xCoord = last (xCoordList L) + dist, yCoord = hd (yCoordList L) - dist\<rparr>,
  \<lparr>xCoord = last (xCoordList L) + dist, yCoord = last (yCoordList L) + dist\<rparr>, \<lparr>xCoord = hd (xCoordList L) - dist, yCoord = last (yCoordList L) + dist\<rparr>,
  \<lparr>xCoord = hd (xCoordList L) - dist, yCoord = hd (yCoordList L) - dist\<rparr>]"
  apply (cut_tac L=L in rBoxPointList, assumption)
  apply (auto simp add: rBox_def polygon_def)
done
(*rBox ist ein Convexes Polygon*)
lemma rBoxConvex : "pointList L \<Longrightarrow> conv_polygon (rBox L)"
  apply (cut_tac L=L in rBoxPointList, assumption)
  apply (simp add: rBox_def)
  apply (cut_tac L="[\<lparr>xCoord = hd (xCoordList L) - 1, yCoord = hd (yCoordList L) - 1\<rparr>, \<lparr>xCoord = last (xCoordList L) + 1, yCoord = hd (yCoordList L) - 1\<rparr>,
     \<lparr>xCoord = last (xCoordList L) + 1, yCoord = last (yCoordList L) + 1\<rparr>, \<lparr>xCoord = hd (xCoordList L) - 1, yCoord = last (yCoordList L) + 1\<rparr>]"
     and P="rBox L" in conv_polygon_def)
  apply (simp)
  apply (simp add: rBox_def)
  apply (simp add: conv_polygon_def polygon_def)
  apply (rule disjI2)
  apply (rule conjI)
  apply (simp add: signedArea_def)
  apply (cases "last (xCoordList L) - hd (xCoordList L) \<ge> 0")
  apply (cases "last (yCoordList L) - hd (yCoordList L) \<ge> 0")
  apply (simp)
  apply (simp add: yCoordSorted1)
  apply (simp add: xCoordSorted1)
  apply (rule conjI)
  apply (simp add: signedArea_def)
  apply (cases "last (xCoordList L) - hd (xCoordList L) \<ge> 0")
  apply (cases "hd (yCoordList L) - last (yCoordList L) \<le> 0")
  apply (simp)
sorry
  
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
  apply (cut_tac L=L in  rBox1, assumption)
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
