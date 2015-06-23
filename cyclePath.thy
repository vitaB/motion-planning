theory cyclePath
imports segmentList
begin

(*geschlossener Pfad*)
definition cyclePath :: "point2d list \<Rightarrow> point2d list" where
  "pointList P \<Longrightarrow> cyclePath P \<equiv> P @ [hd P]"
lemma [simp]: "pointList L \<Longrightarrow> hd L \<noteq> last L" by (cases L, auto simp add: pointList_def)
lemma [simp] : "pointList L \<Longrightarrow> length (cyclePath L) = length L + 1" by (simp add: cyclePath_def)

(*alle Kanten von cyclePath sind segmente*)
lemma cyclePathLastSegment : "pointList L \<Longrightarrow> segment (last L) (last (cyclePath L))"
  apply (simp add: cyclePath_def segment_def, subst neq_commute, simp)
done
theorem cyclePathSegments : "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> i < length P - 1 \<Longrightarrow> segment (P!i) (P! Suc i)"
  apply (unfold cyclePath_def, simp)
  apply (cut_tac L=L and a="hd L" in pointsSegmentsAppend1, simp)
  apply (simp add: segment_def, cases L, auto simp add: pointList_def)
done
  
(*intersection(cyclePath, Strecke A B)*)
fun lineCyclePathInters :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "lineCyclePathInters [] P R = False"
| "lineCyclePathInters [a] P R = False"
| "lineCyclePathInters (a#b#xs) P R = (segment P R \<and> (intersect a b P R \<or> lineCyclePathInters (b#xs) P R))"
(*some simple Lemmas. Erleichtert die Beweisführung*)
lemma lineCyclePathIntersSimp [simp]: "segment A B \<Longrightarrow> \<not>lineCyclePathInters (b#L) A B \<Longrightarrow> lineCyclePathInters (a#b#L) A B = lineCyclePathInters [a,b] A B"
  by (simp)
lemma lineCyclePathIntersSimp1 [simp]: "segment A B \<Longrightarrow> length L \<ge> 1 \<Longrightarrow> \<not> lineCyclePathInters (b#L) A B \<Longrightarrow> \<not>intersect b (hd L) A B"
  by (cases L, auto)
lemma lineCyclePathIntersSimp2 [simp]: "segment A B \<Longrightarrow> \<not>lineCyclePathInters [a,b] A B \<Longrightarrow> lineCyclePathInters (a#b#L) A B = lineCyclePathInters (b#L) A B"
  by (simp)
lemma lineCyclePathIntersNeg : "segment A B \<Longrightarrow> \<not>lineCyclePathInters (a#b#L) A B \<Longrightarrow> \<not>lineCyclePathInters [a,b] A B \<and>  \<not>lineCyclePathInters (b#L) A B"
  by (simp)

(*wann gibt es ein Schnittpunkt zwischen CyclePath und Strecke AB?*)
lemma lineCyclePathInters1: "segment A B \<Longrightarrow> lineCyclePathInters L A B \<Longrightarrow>
  (\<exists> i. i<length L - 1 \<and> intersect (L!i) (L ! Suc i) A B)"
  apply (induct L A B rule:lineCyclePathInters.induct) apply (simp, simp)
  apply (auto, rule_tac x="i + 1" in exI, simp)
done
(*TODO: hier fehlt noch ein Beweis*)
lemma lineCyclePathInters2: "segment A B \<Longrightarrow> (\<exists> i. i < length L - 1 \<and> intersect (L ! i) (L ! Suc i) A B) \<Longrightarrow>
  lineCyclePathInters L A B"
sorry
theorem lineCyclePathIntersEq : "segment A B \<Longrightarrow> lineCyclePathInters L A B =
  (\<exists> i. i < length L - 1 \<and> intersect (L!i) (L ! Suc i) A B)"
  apply (rule iffI, metis lineCyclePathInters1)
  by(metis lineCyclePathInters2)


(*intersection(CyclePath, CyclePath)*)


(*move CyclePath*)





end
