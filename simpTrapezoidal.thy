theory simpTrapezoidal
imports polygon
begin


definition rBox :: "point2d list \<Rightarrow> point2d list" where
"pointList L \<Longrightarrow> rBox L \<equiv> let dist = 1 in [\<lparr>xCoord = hd (xCoordList L) - dist, yCoord = hd (yCoordList L) - dist\<rparr>
 ,\<lparr>xCoord = last (xCoordList L) + dist, yCoord = hd (yCoordList L) - dist\<rparr>, \<lparr>xCoord = last (xCoordList L) + dist, yCoord = last (yCoordList L) + dist\<rparr>,
\<lparr>xCoord = hd (xCoordList L) - dist, yCoord = last (yCoordList L) + dist\<rparr>]"
lemma "pointList L \<Longrightarrow> isPolygon (rBox L)"
  apply (simp add: rBox_def)
sorry

lemma "pointList L \<Longrightarrow> \<forall> a \<in> set L \<longrightarrow> insiedePolygon a (rBox L)"

lemma testab : "pointList L \<Longrightarrow> VARS (xs :: real list) i {pointList L}
  xs := [];
  i := 0;
  WHILE i \<noteq> length L
  INV {\<forall> a. a < i \<longrightarrow> xs!a = (xCoordList L)!a}
  DO
    xs := insort_insert (getX (L!i)) (xs);
    i := i + 1
  OD
  {True}"
  apply(vcg_simp)
  apply (rule allI, rule impI) apply (safe) apply (erule_tac x=a in allE)
  apply (safe) apply (cut_tac x="getX (L ! i)" and xs=xs and a=a in inInsort)
  apply (simp) apply (cut_tac a="(L ! i)" and xs="L" in inXCoord, simp)
  apply (erule_tac x=a in allE, auto)
sorry

(*Welche TrapezStrecken schneiden das Segment*)
(*ich brauche doch segment-datentypen?*)
fun trapezInter :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> real list" where
  "trapezInter [] A B = []"
 | " trapezInter [p] A B = []"
  | "trapezInter (p#r#xs) A B = (if (segment A B \<and> intersect A B p r) then (getX p # trapezInter xs A B) else trapezInter xs A B)"

(*S = Menge von Strecken. keine gleiche x-Koordinate. Strecken Kreuzugsfrei*)
fun trapezoidalMap ::  "point2d list \<Rightarrow> real list" where
"trapezoidalMap [] = []"
| "trapezoidalMap (x#xs) = insort_insert (getX x) (trapezoidalMap xs)"


end
