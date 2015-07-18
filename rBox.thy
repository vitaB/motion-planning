theory rBox
imports polygon
begin

(*es gibt kein Punkt in der Punkt Liste, mit gleicher xCoordinate*)
definition uniqueXCoord :: "point2d list \<Rightarrow> bool" where
  "uniqueXCoord L \<equiv> \<forall> a b. a \<noteq> b \<longrightarrow> xCoord (L!a) \<noteq> xCoord (L!b)"
lemma "3 \<le> length L \<Longrightarrow> uniqueXCoord L \<Longrightarrow> pointList (L)"
  apply (simp add: uniqueXCoord_def pointList_def)
by (metis distinct_conv_nth)

(*4eckige Box um pointListen herum ist selbst eine pointList*)
lemma rBoxPointList: "pointLists PL \<Longrightarrow> pointList(
  [Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1, yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (last (yCoordSort (concat PL))) + 1),
  Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1,yCoord (last (yCoordSort (concat PL))) + 1)])"
sorry

(*Definition wann R eine rechteckige Box um P ist*)
definition rBoxS :: "point2d list \<Rightarrow> point2d list \<Rightarrow> bool" where
  "pointList R \<Longrightarrow> rBoxS R P \<equiv> length R = 4 \<and> cPolygon (cyclePath R) \<and>
  (\<forall> i < length P. pointInsideCPolygonACl (cyclePath R) (P!i))"

(*4eckige Box um pointListen herum*)
definition rBox :: "(point2d list) list \<Rightarrow> point2d list" where
  "pointLists PL \<Longrightarrow> rBox PL \<equiv>
  cyclePath([Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1, yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (last (yCoordSort (concat PL))) + 1),
  Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1,yCoord (last (yCoordSort (concat PL))) + 1)])"

(*ersetzte den Term Polygon im Satz*)
lemma rBoxPoly [simp] : "pointLists PL \<Longrightarrow>
  cyclePath([Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1, yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (last (yCoordSort (concat PL))) + 1),
  Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1,yCoord (last (yCoordSort (concat PL))) + 1)])
  \<equiv> [Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1, yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (last (yCoordSort (concat PL))) + 1),
  Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1,yCoord (last (yCoordSort (concat PL))) + 1),
  Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1, yCoord (hd (yCoordSort (concat PL))) - 1)]"
  apply (cut_tac PL=PL in rBoxPointList, assumption)
  apply (auto simp add: rBox_def cyclePath_def)
done

lemma rBoxCollinearFree[simp] : "pointLists PL \<Longrightarrow> \<not>collinearList (rBox PL)"
sorry

(*rBox ist ein Convexes Polygon*)
lemma rBoxConvex : "pointLists PL \<Longrightarrow> polygon (rBox PL)"  
oops

(*alle Punkte von PL sind innerhalb von rBox PL*)
lemma "pointLists PL \<Longrightarrow> \<forall> a \<in> set L. pointInsidePolygon (rBox PL) a"
  apply (cut_tac PL=PL in rBoxConvex, assumption)
oops



end
