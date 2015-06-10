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
  apply (simp add: polygon_def segment_def)
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
lemma linePolygonIntersSimp [simp]: "segment A B \<Longrightarrow> \<not>linePolygonInters (b#L) A B \<Longrightarrow> linePolygonInters (a#b#L) A B = linePolygonInters [a,b] A B"
  by (simp)
lemma linePolygonIntersSimp1 [simp]: "segment A B \<Longrightarrow> length L \<ge> 1 \<Longrightarrow> \<not> linePolygonInters (b#L) A B \<Longrightarrow> \<not>intersect b (hd L) A B"
  by (cases L, auto)
lemma linePolygonIntersSimp2 [simp]: "segment A B \<Longrightarrow> \<not>linePolygonInters [a,b] A B \<Longrightarrow> linePolygonInters (a#b#L) A B = linePolygonInters (b#L) A B"
  by (simp)
lemma linePolygonIntersNeg : "segment A B \<Longrightarrow> \<not>linePolygonInters (a#b#L) A B \<Longrightarrow> \<not>linePolygonInters [a,b] A B \<and>  \<not>linePolygonInters (b#L) A B"
  by (simp)

(*wann gibt es ein Schnittpunkt zwischen Polygon und Strecke AB?*)
lemma linePolygonInters1: "segment A B \<Longrightarrow> linePolygonInters L A B \<longrightarrow>
  (\<exists> i. intersect (L ! i) (L ! Suc i) A B)"
  apply (induct L A B rule:linePolygonInters.induct) apply (simp, simp)
  apply (auto) apply (rule_tac x=0 in exI, simp)
  apply (rule_tac x="i + 1" in exI, simp)
by (metis nth_Cons_Suc)
(**************TODO*)
lemma linePolygonIntersSimp3 [simp]: "segment A B \<Longrightarrow>  length L \<ge> 1 \<Longrightarrow> \<not> linePolygonInters (a # L) A B
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
lemma linePolygonIntersSimp3 [simp]: "segment A B \<Longrightarrow> length xs \<ge> 1 \<Longrightarrow> intersect ((a # b # xs) ! i) ((a # b # xs) ! Suc i) A B \<Longrightarrow>
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





end
