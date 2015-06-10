theory simpTrapezoidal
imports polygon
begin

(*4eckige Box um pointListe herum ist selbst eine pointList*)
lemma rBoxPointList: "pointList L \<Longrightarrow> 
 pointList ([Abs_point2d(xCoord (hd (xCoordSort L)) - 1, yCoord (hd (yCoordSort L)) - 1),
  Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (hd (yCoordSort L)) - 1),Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (last (yCoordSort L)) + 1),
  Abs_point2d(xCoord (hd (xCoordSort L)) - 1,yCoord (last (yCoordSort L)) + 1)])"
sorry
(*4eckige Box um pointListe herum*)
definition rBox :: "point2d list \<Rightarrow> point2d list" where
"pointList L \<Longrightarrow> rBox L \<equiv> polygon([Abs_point2d(xCoord (hd (xCoordSort L)) - 1, yCoord (hd (yCoordSort L)) - 1),
  Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (hd (yCoordSort L)) - 1),Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (last (yCoordSort L)) + 1),
  Abs_point2d(xCoord (hd (xCoordSort L)) - 1,yCoord (last (yCoordSort L)) + 1)])"

(*ersetzte den Term Polygon im Satz*)
lemma rBoxPoly [simp] : "pointList L \<Longrightarrow>
  polygon([Abs_point2d(xCoord (hd (xCoordSort L)) - 1, yCoord (hd (yCoordSort L)) - 1),
  Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (hd (yCoordSort L)) - 1),Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (last (yCoordSort L)) + 1),
  Abs_point2d(xCoord (hd (xCoordSort L)) - 1,yCoord (last (yCoordSort L)) + 1)])
  \<equiv> [Abs_point2d(xCoord (hd (xCoordSort L)) - 1, yCoord (hd (yCoordSort L)) - 1),
  Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (hd (yCoordSort L)) - 1),Abs_point2d(xCoord (last (xCoordSort L)) + 1,yCoord (last (yCoordSort L)) + 1),
  Abs_point2d(xCoord (hd (xCoordSort L)) - 1,yCoord (last (yCoordSort L)) + 1), Abs_point2d(xCoord (hd (xCoordSort L)) - 1,yCoord (hd (yCoordSort L)) - 1)]"
  apply (cut_tac L=L in rBoxPointList, assumption)
  apply (auto simp add: rBox_def polygon_def)
done

(*rBox ist ein Convexes Polygon*)
lemma rBoxConvex : "pointList L \<Longrightarrow> conv_polygon (rBox L)"
  apply (cut_tac L=L in rBoxPointList, assumption)
  apply (simp add: rBox_def)
  apply (simp add: conv_polygon_def) 
  apply (rule disjI2)
  apply (auto simp add: signedArea_def)
  apply (subgoal_tac "xCoord (last (xCoordSort L)) - xCoord (hd (xCoordSort L)) \<ge> 0")
  apply (subgoal_tac "yCoord (last (yCoordSort L)) - yCoord (hd (yCoordSort L)) \<ge> 0", simp)
  apply (auto simp add: le_diff_eq yCoordOrd xCoordOrd)
  apply (subgoal_tac "xCoord (last (xCoordSort L)) - xCoord (hd (xCoordSort L)) \<ge> 0")
  apply (subgoal_tac "yCoord (hd (yCoordSort L)) - yCoord (last (yCoordSort L)) \<le> 0")
  apply (simp add: mult_less_0_iff)
  apply (auto simp add: yCoordOrd le_diff_eq xCoordOrd)
  apply (subgoal_tac "xCoord (last (xCoordSort L)) - xCoord (hd (xCoordSort L)) \<ge> 0")
  apply (subgoal_tac "yCoord (last (yCoordSort L)) - yCoord (hd (yCoordSort L)) \<ge> 0", simp)
  apply (auto simp add: le_diff_eq yCoordOrd xCoordOrd)
done

(*alle Punkte von L sind innerhalb von rBox L*)
lemma "pointList L \<Longrightarrow> \<forall> a \<in> set L. insidePolygonACl (rBox L) a"
  apply (cut_tac L=L in rBoxConvex, assumption)
  apply (simp add: insidePolygonACl_def)
  apply (simp add: rBox_def)
oops

(*Welche TrapezStrecken schneiden das Segment*)
(*ich brauche doch ein segment-datentypen?*)
fun trapezInter :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> real list" where
  "trapezInter [] A B = []"
 | "trapezInter [p] A B = []"
 | "trapezInter (p#r#xs) A B = (if (segment A B \<and> intersect A B p r) then (xCoord p # trapezInter xs A B) else trapezInter xs A B)"

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
