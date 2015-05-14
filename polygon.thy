theory polygon
imports segmentList
begin

(*Polygon. mit mehr als 3 Ecken. und Kreislauf*)
definition polygon :: "point2d list \<Rightarrow> point2d list" where
"pointList P \<Longrightarrow> polygon P \<equiv> P @ [hd P]"

lemma isPolygon : "pointList P  \<Longrightarrow> distinct P \<and> size (polygon P) \<ge> 4 \<and> hd P = last (polygon P)"
by (induct P, auto simp add: polygon_def pointList_def)

(*wann ist ein polygon convex?*)
(*conv. Polygone die im Uhrzeigersinn gespeichert werden, werden damit nicht erkannt!*)
fun pointsACl :: "point2d list \<Rightarrow> bool" where 
  "pointsACl [] = True"
|  "pointsACl [a] = True"
|  "pointsACl [a,b] = True"
|  "pointsACl (a#b#c#xs) = (signedArea a b c > 0 \<and> pointsACl (b#c#xs))"
fun pointsCl :: "point2d list \<Rightarrow> bool" where 
  "pointsCl [] = True"
|  "pointsCl [a] = True"
|  "pointsCl [a,b] = True"
|  "pointsCl (a#b#c#xs) = (signedArea a b c < 0 \<and> pointsCl (b#c#xs))"
lemma pointsClRev : "pointList P \<Longrightarrow> pointsCl P \<longleftrightarrow> pointsACl (rev P)"
  apply (rule iffI)
  (*apply (cases P rule: pointsCl.cases)
  apply (auto)*)
  apply (cases P rule: pointsCl.cases)
  apply (auto)
sorry

definition conv_polygon :: "point2d list \<Rightarrow> bool" where
"pointist L \<Longrightarrow> P = polygon L \<Longrightarrow> conv_polygon P \<equiv> (pointsCl P \<or> pointsACl P)"

(*definition poly1 :: "point2d list" where
"poly1 \<equiv> [(| xCoord = 0, yCoord = 0 |),(| xCoord = 2, yCoord = 1 |),(| xCoord = 3, yCoord = 2 |),(| xCoord = 1, yCoord = 3 |)]"
definition poly2 :: "point2d list" where
"poly2 \<equiv> polygon poly1"
lemma "trapezoidalMap poly2 = [0,1,2,3]"
apply (simp add: poly2_def poly1_def)
apply (simp add: polygon_def pointList_def del: trapezoidalMap.simps)
apply (simp add: insort_insert_insort)
apply (simp add: insort_insert_triv)
done
lemma "conv_polygon (polygon poly1)"
 apply (subgoal_tac "pointList poly1")
 apply (simp add: polygon_def conv_polygon_def, rule disjI2)
 apply (auto simp add: poly1_def signedArea_def)
 apply (simp add: pointList_def)
done*)


(*Punkt inside Polygon*)


(*Punkt outside Polygon*)


(*intersection(Polygon, Strecke A B)*)
fun linePolygonInters :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "linePolygonInters [] P R = False"
| "linePolygonInters [a] P R = False"
| "linePolygonInters (a#b#xs) P R = (segment P R \<and> (intersect a b P R \<or> linePolygonInters xs P R))"
lemma "pointist L \<Longrightarrow> P = polygon L \<Longrightarrow> segment A B \<Longrightarrow> linePolygonInters P A B \<longleftrightarrow> (\<exists> i j. 0 \<le> i \<and> i < j \<and> j \<le> size L \<longrightarrow>
  intersect (nth P i) (nth P j) A B)"
  apply (rule iffI)
  apply (rule_tac x="(P ,A, B)" in linePolygonInters.cases)
  apply (simp, simp)
  apply (simp)
sorry


(*wenn ein punkt einer Strecke inside Polygon und ein Punkt einer Strecke outside, dann gibt es eine intersection*)


(*intersection(Polygon, Polygon)*)


(*move Polygon*)




(* Line/Segment soll kein eigener Datentyp mehr sein!
lemma polygonCompl : "pointList P \<Longrightarrow> L = segList P \<Longrightarrow> R = segList(polygon P) \<Longrightarrow> a \<in> set(L) \<longrightarrow> a \<in> set(R)"
  apply (auto)
  apply (cut_tac P=P and p="[hd P]" and a=a in segListapp)
  apply (auto simp add: pointList_def polygon_def)
done

lemma polygonCompl1 : "pointList P \<Longrightarrow> L = segList P \<Longrightarrow> R = segList(polygon P) \<Longrightarrow> (a = \<lparr>sPoint= last P, ePoint= hd P\<rparr> \<or> a \<in> set(L)) \<longleftrightarrow> a \<in> set(R)"
sorry

lemma segmentPolygon [simp] : "pointList P \<Longrightarrow> R = segList(polygon P) \<Longrightarrow> a \<in> set(R) \<longrightarrow> segment a"
  apply (simp add: polygon_def pointList_def)
  apply (induct_tac rule: segList.induct)
  apply (simp, simp)
  apply (erule impE)
  apply (simp add: segment_def)

  apply (simp add: polygon_def pointList_def)
  apply (cases "a \<in> set (segList (P))")
  apply (cut_tac P=P and a=a and p="[hd P]" in segListapp)
  apply (simp add: pointList_def, assumption)
  apply (cut_tac P=P and L="segList P" and a=a in segmentList)
  apply (simp add: pointList_def, simp+)
  apply (rule_tac x = P in segList.cases, simp, simp)
  apply (safe)
  apply (simp only: List.list.sel(1))
sorry
  

(*kein segment wiederholt sich*)
lemma segPolygonDistinct : "pointList P \<Longrightarrow> R = segList(polygon P) \<Longrightarrow> a \<in> set(R) \<and> b \<in> set(R) \<and> a \<noteq> b
  \<longrightarrow> sPoint(a) \<noteq> sPoint(b) \<and> ePoint(a) \<noteq> ePoint(b)"
  apply (simp)
  apply (rule impI, rule conjI,erule conjE, erule conjE)
  apply (cut_tac P=P and R = R and a=a in segmentPolygon)
  apply (assumption+)
  apply (erule impE)
  apply (simp)
  apply (cut_tac P=P and R = R and a=b in segmentPolygon)
  apply (assumption+)
  apply (erule impE)
  apply (simp)
thm segListdistinct
  apply (cut_tac P=P and L=R and a=a and b=b in segListdistinct)
  apply (assumption)
  apply (simp add: segment_def)
sorry

(*Beweis: Kreislauf mit Punkten wo Anfangspunkt und Endpunk gleich sind. mehr als 2 Ecken
definition circuit_list :: "line list \<Rightarrow> bool" where
"connected segList \<Longrightarrow> circuit_list segList = (sPoint(hd segList) = ePoint (last segList))"*)


(*definition polygon_eq :: "line list \<Rightarrow> line list \<Rightarrow> bool" where
"polygon_eq P R \<equiv> list_eq_iff_nth_eq P R"*)


(*intersection(Polygon, Line)*)
definition lineIntersect :: "point2d list \<Rightarrow> line \<Rightarrow> bool" where
"pointList P  \<Longrightarrow> segment l \<Longrightarrow> lineIntersect P l \<equiv> (\<exists> a ::line. a \<in> set(segList(polygon P))
\<and> intersect l a)"

lemma "pointList P  \<Longrightarrow> L = segList P \<Longrightarrow> \<forall> a::line. a \<in> set L \<longrightarrow> lineIntersect P a"
  apply (auto simp add: lineIntersect_def pointList_def)
  apply (rule_tac x=a in exI)
  apply (rule conjI)
  apply (cut_tac P=P and L="segList P" and R = "segList (polygon P)" in polygonCompl)
  apply (auto simp add: intersect_def pointList_def)
done
*)
(*lemma even_induct:
assumes "even n"
shows "P 0 \<Longrightarrow> ( \<And>m. Q m \<Longrightarrow> P (Suc m)) \<Longrightarrow> (\<And>m. P m \<Longrightarrow> Q (Suc m)) \<Longrightarrow> P n"
apply(atomize (full))
apply(cut_tac assms)
apply(unfold even_def)
apply(drule spec[where x=P])
apply(drule spec[where x=Q])
apply(assumption)
done*)
end
