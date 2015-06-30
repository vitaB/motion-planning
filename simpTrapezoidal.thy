theory simpTrapezoidal
imports polygon
begin

(*4eckige Box um pointListe herum ist selbst eine pointList*)
lemma simpRBoxPointList: "pointList L \<Longrightarrow> 
 pointList ([Abs_point2d(xCoord (hd (xCoordSort L)) - 1, yCoord (hd (yCoordSort L)) - 1),
  Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (hd (yCoordSort L)) - 1),Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (last (yCoordSort L)) + 1),
  Abs_point2d(xCoord (hd (xCoordSort L)) - 1,yCoord (last (yCoordSort L)) + 1)])"
sorry
(*4eckige Box um pointListe herum*)
definition simpRBox :: "point2d list \<Rightarrow> point2d list" where
"pointList L \<Longrightarrow> simpRBox L \<equiv> cyclePath([Abs_point2d(xCoord (hd (xCoordSort L)) - 1, yCoord (hd (yCoordSort L)) - 1),
  Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (hd (yCoordSort L)) - 1),Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (last (yCoordSort L)) + 1),
  Abs_point2d(xCoord (hd (xCoordSort L)) - 1,yCoord (last (yCoordSort L)) + 1)])"

(*ersetzte den Term Polygon im Satz*)
lemma simpRBoxPoly [simp] : "pointList L \<Longrightarrow>
  cyclePath([Abs_point2d(xCoord (hd (xCoordSort L)) - 1, yCoord (hd (yCoordSort L)) - 1),
  Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (hd (yCoordSort L)) - 1),Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (last (yCoordSort L)) + 1),
  Abs_point2d(xCoord (hd (xCoordSort L)) - 1,yCoord (last (yCoordSort L)) + 1)])
  \<equiv> [Abs_point2d(xCoord (hd (xCoordSort L)) - 1, yCoord (hd (yCoordSort L)) - 1),
  Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (hd (yCoordSort L)) - 1),Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (last (yCoordSort L)) + 1),
  Abs_point2d(xCoord (hd (xCoordSort L)) - 1,yCoord (last (yCoordSort L)) + 1), Abs_point2d(xCoord (hd (xCoordSort L)) - 1,yCoord (hd (yCoordSort L)) - 1)]"
  apply (cut_tac L=L in simpRBoxPointList, assumption)
  apply (auto simp add: simpRBox_def cyclePath_def)
done

(*simpRBox ist ein Convexes Polygon*)
lemma simpRBoxConvex : "pointList L \<Longrightarrow> polygon (simpRBox L)"  
sorry

(*alle Punkte von L sind innerhalb von simpRBox L*)
lemma "pointList L \<Longrightarrow> \<forall> a \<in> set L. insidePolygonACl (simpRBox L) a"
  apply (cut_tac L=L in simpRBoxConvex, assumption)
oops

definition uniqueXCoord :: "point2d list \<Rightarrow> bool" where
  "uniqueXCoord L \<equiv> \<forall> a b. a \<noteq> b \<longrightarrow> xCoord (L!a) \<noteq> xCoord (L!b)"

(*vertikale Strecken einzeichnen. Eingabe Polygon(ohne last) und simpRBox*)
fun trapezoidal :: "point2d list \<Rightarrow> point2d list \<Rightarrow> point2d list" where
  "trapezoidal [] R  = []"
  | "trapezoidal (x#xs) R = [x , Abs_point2d(xCoord x, yCoord (last (yCoordSort R))),
      x , Abs_point2d(xCoord x, yCoord (hd (yCoordSort R)))] @ trapezoidal xs R"

(*ersetzte Trapez. AB ist ein Segment aus dem Polygon. p ist der "entstehungsknoten" des slab
(schnittpunkt zwischen pr und AB)*)
definition newTrapez :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d list" where
  "newTrapez p A B \<equiv> [(Abs_point2d (xCoord p, (lineFunktionY A B (xCoord p)))), p]"

(*welche Trapeze schneiden segment AB. ersetzte gefundene Trapeze, andere bleiben unberührt.*)
fun trapezInter :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d list" where
  "trapezInter [] A B  = []"
  | "trapezInter [p] A B = []"
  | "trapezInter (p#r#xs) A B =
  (if (leftFromSegment A B p) then (
    (if (segment A B \<and> intersect A B p r) then ((newTrapez p A B) @ trapezInter xs A B)
    else (p#r # trapezInter xs A B)) )
  else [])"

fun trapezoidalMap :: "point2d list \<Rightarrow> point2d list \<Rightarrow> point2d list" where
  "trapezoidalMap _ [] = []"
  | "trapezoidalMap _ [p] = []"
  | "trapezoidalMap T (p#r#xs) = trapezoidalMap (trapezInter T p r) xs"

(*definition trapezoidalMap :: "point2d list \<Rightarrow> point2d list \<Rightarrow> point2d list" where
  "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> R = simpRBox L \<Longrightarrow>
  uniqueXCoord L \<Longrightarrow> T=trapezoidal L R \<Longrightarrow> trapezoidalMap P T \<equiv> \<forall> i. i < length P - 1 \<longrightarrow>
  (trapezInter T (P!i) (P!Suc i))  newTrapez p (P!i) (P!Suc i))
  ersetzteTrapez(findeGeschnittenTrapez mit L!i, newTrapez p (P!i) (P!Suc i) )"*)

(*
(*Welche TrapezStrecken schneiden das Segment*)
(*ich brauche doch ein segment-datentypen?*)
fun trapezInter :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> real list" where
  "trapezInter [] A B = []"
 | "trapezInter [p] A B = []"
 | "trapezInter (p#r#xs) A B = (if (segment A B \<and> intersect A B p r) then (xCoord p # trapezInter xs A B) else trapezInter xs A B)"*)

(*S = Menge von Strecken. keine gleiche x-Koordinate. Strecken Kreuzugsfrei*)
(*fun trapezoidalMap ::  "point2d list \<Rightarrow> real list" where
"trapezoidalMap [] = []"
| "trapezoidalMap (x#xs) = insort_insert (xCoord x) (trapezoidalMap xs)"*)







(*alte Definition!*)
(*(*4eckige Box um pointListe herum ist selbst eine pointList*)
lemma rBoxPointList: "pointList L \<Longrightarrow> 
  pointList ([\<lparr>xCoord = hd (xCoordList L) - 1, yCoord = hd (yCoordList L) - 1\<rparr> ,\<lparr>xCoord = last (xCoordList L) + 1, yCoord = hd (yCoordList L) - 1\<rparr>,
  \<lparr>xCoord = last (xCoordList L) + 1, yCoord = last (yCoordList L) + 1\<rparr>,\<lparr>xCoord = hd (xCoordList L) - 1, yCoord = last (yCoordList L) + 1\<rparr>])"
  apply (cut_tac P=L in YCoordSort)
  apply (cut_tac P=L in XCoordSort)
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
*)
(*(*ersetzte den Term Polygon im Satz*)
lemma rBoxPoly [simp] : "pointList L \<Longrightarrow>
  (polygon([\<lparr>xCoord = hd (xCoordList L) - 1, yCoord = hd (yCoordList L) - 1\<rparr>,\<lparr>xCoord = last (xCoordList L) + 1, yCoord = hd (yCoordList L) - 1\<rparr>,
  \<lparr>xCoord = last (xCoordList L) + 1, yCoord = last (yCoordList L) + 1\<rparr>,\<lparr>xCoord = hd (xCoordList L) - 1, yCoord = last (yCoordList L) + 1\<rparr>]))
  \<equiv> [\<lparr>xCoord = hd (xCoordList L) - 1, yCoord = hd (yCoordList L) - 1\<rparr> ,\<lparr>xCoord = last (xCoordList L) + 1, yCoord = hd (yCoordList L) - 1\<rparr>,
  \<lparr>xCoord = last (xCoordList L) + 1, yCoord = last (yCoordList L) + 1\<rparr>, \<lparr>xCoord = hd (xCoordList L) - 1, yCoord = last (yCoordList L) + 1\<rparr>,
  \<lparr>xCoord = hd (xCoordList L) - 1, yCoord = hd (yCoordList L) - 1\<rparr>]"
  apply (cut_tac L=L in rBoxPointList, assumption)
  apply (auto simp add: rBox_def polygon_def)
done
*)
(*(*rBox ist ein Convexes Polygon*)
lemma rBoxConvex : "pointList L \<Longrightarrow> conv_polygon (rBox L)"
  apply (cut_tac L=L in rBoxPointList, assumption)
  apply (simp add: rBox_def)
  apply (simp add: conv_polygon_def)  
  apply (rule disjI2)
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
*)
end
