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
fun slabs :: "point2d list \<Rightarrow> point2d list \<Rightarrow> point2d list" where
  "slabs [] R  = []"
  | "slabs (x#xs) R = [x , Abs_point2d(xCoord x, yCoord (last (yCoordSort R))),
      x , Abs_point2d(xCoord x, yCoord (hd (yCoordSort R)))] @ slabs xs R"

(*mit der slabs lässt sich jeder Punkt in simpRBoxPointList finden*)
(*slabs und trapeze müssten dafür als datentyp gespeichert werden (?)*)

(*ersetzte Trapez. AB ist ein Segment aus dem Polygon. p ist der "entstehungsknoten" des slab
(schnittpunkt zwischen pr und AB)*)
definition newTrapez :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d list" where
  "newTrapez p A B \<equiv> [p, Abs_point2d (xCoord p, (lineFunktionY A B (xCoord p)))]"

(*welche Trapeze schneiden segment AB. ersetzte gefundene Trapeze, andere bleiben unberührt.*)
fun trapezInter :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d list" where
  "trapezInter [] A B  = []"
  | "trapezInter [p] A B = []"
  | "trapezInter (p#r#xs) A B =
  (if (leftFromSegment A B p) then (
    (if (segment A B \<and> crossing A B p r) then (
      (newTrapez p A B) @ trapezInter xs A B)
    else (p#r # trapezInter xs A B))
  ) else (p#r#xs))"

fun trapezoidalMap :: "point2d list \<Rightarrow> point2d list \<Rightarrow> point2d list" where
  "trapezoidalMap _ [] = []"
  | "trapezoidalMap _ [p] = []"
  | "trapezoidalMap T (p#r#xs) = trapezoidalMap (trapezInter T p r) xs"
(*definition trapezoidalMap :: "point2d list \<Rightarrow> point2d list \<Rightarrow> point2d list" where
  "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> R = simpRBox L \<Longrightarrow>
  uniqueXCoord L \<Longrightarrow> T=trapezoidal L R \<Longrightarrow> trapezoidalMap P T \<equiv> \<forall> i. i < length P - 1 \<longrightarrow>
  (trapezInter T (P!i) (P!Suc i))  newTrapez p (P!i) (P!Suc i))
  ersetzteTrapez(findeGeschnittenTrapez mit L!i, newTrapez p (P!i) (P!Suc i) )"*)


(*entferne die übrigen strecken die noch innerhalb der Polygone sind*)

(*zeige das keine der segmente von trapezodialMap das polygon innerhalb von rBox nicht schneidet*)

(*zeige das die trapezoidalMap jetzt eine Einteilung der Freien-Räume innerhalb der rBox ist*)







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
*)
end
