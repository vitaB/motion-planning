theory cyclePath
imports segmentList
begin

(*geschlossener Pfad*)
definition cyclePath :: "point2d list \<Rightarrow> point2d list" where
"pointList P \<Longrightarrow> cyclePath P \<equiv> P @ [hd P]"
lemma [simp]: "pointList L \<Longrightarrow> hd L \<noteq> last L" by (cases L, auto simp add: pointList_def)

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
lemma lineCyclePathInters1: "segment A B \<Longrightarrow> lineCyclePathInters L A B \<longrightarrow>
  (\<exists> i. intersect (L ! i) (L ! Suc i) A B)"
  apply (induct L A B rule:lineCyclePathInters.induct) apply (simp, simp)
  apply (auto) apply (rule_tac x=0 in exI, simp)
  apply (rule_tac x="i + 1" in exI, simp)
by (metis nth_Cons_Suc)
(*lemma lineCyclePathIntersSimp3 [simp]: "segment A B \<Longrightarrow> length L \<ge> 1 \<Longrightarrow> \<not> lineCyclePathInters (a # L) A B
    \<Longrightarrow> \<not> intersect ((a # L) ! i) ((a # L) ! Suc i) A B"
    apply (subgoal_tac "\<not> intersect a (hd L) A B")
    apply (induct L A B rule:lineCyclePathInters.induct, simp, simp)
    apply (cases i, simp, simp)  
oops*)
(*lemma intersectNeg : "segment A B  \<Longrightarrow>
  \<not> lineCyclePathInters L A B \<longrightarrow> \<not>(\<exists> i. intersect (L ! i) (L ! Suc i) A B)"
  apply (rule ccontr)
  apply (induct L A B rule:lineCyclePathInters.induct) apply (safe)
  apply (auto) 
oops*)
lemma lineCyclePathInters2: "segment A B \<Longrightarrow> length L \<ge> 2 \<Longrightarrow> (intersect (L ! i) (L ! Suc i) A B) \<Longrightarrow> lineCyclePathInters L A B"
  apply (induct L A B rule:lineCyclePathInters.induct)
  apply (auto)
  apply (subgoal_tac "intersect ((a # b # xs) ! i) ((b # xs) ! i) P R \<longleftrightarrow> lineCyclePathInters (a # b # xs) P R")
  apply (auto)
  (*apply (cut_tac A=P and B=R and L="(b#xs)" in intersectNeg, auto)
by (metis nth_Cons')*)
sorry
(*lemma lineCyclePathIntersSimp3 [simp]: "segment A B \<Longrightarrow> length xs \<ge> 1 \<Longrightarrow> intersect ((a # b # xs) ! i) ((a # b # xs) ! Suc i) A B \<Longrightarrow>
  \<not> lineCyclePathInters (b # xs) A B \<Longrightarrow> lineCyclePathInters [a,b] A B"
  apply (simp)
  apply (cut_tac A=A and B=B and a=a and b=b and L=xs and k=i in listIntersection, simp, simp)
  apply (simp) 
oops*)
theorem lineCyclePathIntersEquiv : "segment A B \<Longrightarrow> length L \<ge> 2 \<Longrightarrow> lineCyclePathInters L A B \<longleftrightarrow>
  (\<exists> i. intersect (L ! i) (L ! Suc i) A B)"
  by (auto simp add: lineCyclePathInters1 lineCyclePathInters2)


(*intersection(CyclePath, CyclePath)*)


(*move CyclePath*)





end
