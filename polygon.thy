theory polygon
imports segmentList
begin

(*Polygon. mit mehr als 3 Ecken. und Kreislauf*)
(*polygon kann sich hier noch überschneiden*)
definition polygon :: "point2d list \<Rightarrow> point2d list" where
"pointList P \<Longrightarrow> polygon P \<equiv> P @ [hd P]"

(*alle Kanten von polygon sind segmente*)
lemma [simp]: "pointList L \<Longrightarrow> hd L \<noteq> last L"
  by (cases L, auto simp add: pointList_def)
lemma polygonLastSegment : "pointList L \<Longrightarrow> segment (last L) (last (polygon L))"
  apply (simp add: polygon_def segment_def pointsEqual1)
  apply (subst neq_commute, simp)
done
theorem polygonSegments : "pointList L \<Longrightarrow> P = polygon L \<Longrightarrow> i < (size P - 1) \<Longrightarrow> segment (P!i) (P!(i+1))"
  apply (unfold polygon_def)
  apply (cut_tac L=L and a="hd L" in pointsSegmentsAppend, auto)
  apply (cut_tac L=L and i=k in pointsSegments, auto)
  apply (cut_tac L=L in polygonLastSegment, auto simp add: polygon_def)
done

lemma isPolygon : "pointList P  \<Longrightarrow> distinct P \<and> size (polygon P) \<ge> 4 \<and> hd P = last (polygon P)"
by (induct P, auto simp add: polygon_def pointList_def)

(*intersection(Polygon, Strecke A B)*)
fun linePolygonInters :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "linePolygonInters [] P R = False"
| "linePolygonInters [a] P R = False"
| "linePolygonInters (a#b#xs) P R = (segment P R \<and> (intersect a b P R \<or> linePolygonInters (b#xs) P R))"
(*some simple Lemmas. Erleichtert die Beweisführung*)
lemma [simp]: "segment A B \<Longrightarrow> \<not>linePolygonInters (b#L) A B \<Longrightarrow> linePolygonInters (a#b#L) A B = linePolygonInters [a,b] A B"
  by (simp)
lemma [simp]: "segment A B \<Longrightarrow> length L \<ge> 1 \<Longrightarrow> \<not> linePolygonInters (b#L) A B \<Longrightarrow> \<not>intersect b (hd L) A B"
  by (cases L, auto)
lemma [simp]: "segment A B \<Longrightarrow> \<not>linePolygonInters [a,b] A B \<Longrightarrow> linePolygonInters (a#b#L) A B = linePolygonInters (b#L) A B"
  by (simp)
lemma "segment A B \<Longrightarrow> \<not>linePolygonInters (a#b#L) A B \<Longrightarrow> \<not>linePolygonInters [a,b] A B \<and>  \<not>linePolygonInters (b#L) A B"
  by (simp)

(*wann gibt es ein Schnittpunkt zwischen Polygon und Strecke AB?*)
lemma linePolygonInters1: "segment A B \<Longrightarrow> linePolygonInters L A B \<longrightarrow>
  (\<exists> i. intersect (L ! i) (L ! Suc i) A B)"
  apply (induct L A B rule:linePolygonInters.induct) apply (simp, simp)
  apply (auto) apply (rule_tac x=0 in exI, simp)
  apply (rule_tac x="i + 1" in exI, simp)
by (metis nth_Cons_Suc)
(**************TODO*)
lemma [simp]: "segment A B \<Longrightarrow>  length L \<ge> 1 \<Longrightarrow> \<not> linePolygonInters (a # L) A B
    \<Longrightarrow> \<not> intersect ((a # L) ! i) ((a # L) ! Suc i) A B"
    apply (cases L, auto)
oops
lemma intersectNeg : "segment A B  \<Longrightarrow>
  \<not> linePolygonInters L A B \<longrightarrow> \<not>(\<exists> i. intersect (L ! i) (L ! Suc i) A B)"
  apply (rule ccontr)
  apply (induct L A B rule:linePolygonInters.induct) apply (safe)
  apply (auto) 
sorry  
(**************TODO*)
lemma linePolygonInters2: "segment A B \<Longrightarrow> length L \<ge> 2 \<Longrightarrow> (intersect (L ! i) (L ! Suc i) A B) \<Longrightarrow> linePolygonInters L A B"
  apply (induct L A B rule:linePolygonInters.induct)
  apply (auto)
  apply (subgoal_tac "intersect ((a # b # xs) ! i) ((b # xs) ! i) P R \<longleftrightarrow> linePolygonInters (a # b # xs) P R")
  apply (auto)
  apply (cut_tac A=P and B=R and L="(b#xs)" in intersectNeg, auto)
by (metis nth_Cons')
(**************TODO*)
lemma [simp]: "segment A B \<Longrightarrow> length xs \<ge> 1 \<Longrightarrow> intersect ((a # b # xs) ! i) ((a # b # xs) ! Suc i) A B \<Longrightarrow>
  \<not> linePolygonInters (b # xs) A B \<Longrightarrow> linePolygonInters [a,b] A B"
  apply (simp)
  apply (cut_tac A=A and B=B and a=a and b=b and L=xs and k=i in listIntersection, simp, simp)
  apply (simp) 
oops

theorem linePolygonIntersEquiv : "segment A B \<Longrightarrow> length L \<ge> 2 \<Longrightarrow> linePolygonInters L A B \<longleftrightarrow>
  (\<exists> i. intersect (L ! i) (L ! Suc i) A B)"
  by (auto simp add: linePolygonInters1 linePolygonInters2)


(*wenn ein punkt einer Strecke inside Polygon und ein Punkt einer Strecke outside, dann gibt es eine intersection*)

(*intersection(Polygon, Polygon)*)

(*wann ist ein polygon convex?*)
(*conv. Polygone die im Uhrzeigersinn gespeichert werden, werden damit nicht erkannt!*)
fun pointsACl :: "point2d list \<Rightarrow> bool" where 
  "pointsACl [] = True"
|  "pointsACl [a] = True"
|  "pointsACl [a,b] = True"
|  "pointsACl (a#b#c#xs) = (signedArea a b c > 0 \<and> pointsACl (b#c#xs))"
definition pointsCl :: "point2d list \<Rightarrow> bool" where 
  "pointsCl P \<equiv> pointsACl (rev P)"

definition conv_polygon :: "point2d list \<Rightarrow> bool" where
"pointList L \<Longrightarrow> P = polygon L \<Longrightarrow> conv_polygon P \<equiv> (pointsCl P \<or> pointsACl P)"

(*Punkt inside Polygon. Testweise*)
definition insidePolygonACl :: "point2d list \<Rightarrow> point2d \<Rightarrow> bool" where
"conv_polygon P \<Longrightarrow> insidePolygonACl P a \<equiv> \<forall> i j. 0 \<le> i \<and> j = i + 1 \<and> j < size P \<longrightarrow> signedArea (P!i) (P!j) a > 0"

(*Punkt outside Polygon*)


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
end
