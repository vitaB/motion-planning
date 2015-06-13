theory cohesivePath
imports segmentList
begin

(*geschlossener Pfad*)
definition cohesivePath :: "point2d list \<Rightarrow> point2d list" where
"pointList P \<Longrightarrow> cohesivePath P \<equiv> P @ [hd P]"

(*alle Kanten von cohesivePath sind segmente*)
lemma [simp]: "pointList L \<Longrightarrow> hd L \<noteq> last L"
  by (cases L, auto simp add: pointList_def)
lemma cohesivePathLastSegment : "pointList L \<Longrightarrow> segment (last L) (last (cohesivePath L))"
  apply (simp add: cohesivePath_def segment_def)
  apply (subst neq_commute, simp)
done
theorem cohesivePathSegments : "pointList L \<Longrightarrow> P = cohesivePath L \<Longrightarrow> i < (size P - 1) \<Longrightarrow> segment (P!i) (P!(i+1))"
  apply (unfold cohesivePath_def)
  apply (cut_tac L=L and a="hd L" in pointsSegmentsAppend, auto)
  apply (cut_tac L=L and i=k in pointsSegments, auto)
  apply (cut_tac L=L in cohesivePathLastSegment, auto simp add: cohesivePath_def)
done

(*intersection(cohesivePath, Strecke A B)*)
fun lineCohesivePathInters :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "lineCohesivePathInters [] P R = False"
| "lineCohesivePathInters [a] P R = False"
| "lineCohesivePathInters (a#b#xs) P R = (segment P R \<and> (intersect a b P R \<or> lineCohesivePathInters (b#xs) P R))"
(*some simple Lemmas. Erleichtert die Beweisführung*)
lemma lineCohesivePathIntersSimp [simp]: "segment A B \<Longrightarrow> \<not>lineCohesivePathInters (b#L) A B \<Longrightarrow> lineCohesivePathInters (a#b#L) A B = lineCohesivePathInters [a,b] A B"
  by (simp)
lemma lineCohesivePathIntersSimp1 [simp]: "segment A B \<Longrightarrow> length L \<ge> 1 \<Longrightarrow> \<not> lineCohesivePathInters (b#L) A B \<Longrightarrow> \<not>intersect b (hd L) A B"
  by (cases L, auto)
lemma lineCohesivePathIntersSimp2 [simp]: "segment A B \<Longrightarrow> \<not>lineCohesivePathInters [a,b] A B \<Longrightarrow> lineCohesivePathInters (a#b#L) A B = lineCohesivePathInters (b#L) A B"
  by (simp)
lemma lineCohesivePathIntersNeg : "segment A B \<Longrightarrow> \<not>lineCohesivePathInters (a#b#L) A B \<Longrightarrow> \<not>lineCohesivePathInters [a,b] A B \<and>  \<not>lineCohesivePathInters (b#L) A B"
  by (simp)

(*wann gibt es ein Schnittpunkt zwischen CohesivePath und Strecke AB?*)
lemma lineCohesivePathInters1: "segment A B \<Longrightarrow> lineCohesivePathInters L A B \<longrightarrow>
  (\<exists> i. intersect (L ! i) (L ! Suc i) A B)"
  apply (induct L A B rule:lineCohesivePathInters.induct) apply (simp, simp)
  apply (auto) apply (rule_tac x=0 in exI, simp)
  apply (rule_tac x="i + 1" in exI, simp)
by (metis nth_Cons_Suc)
(*lemma lineCohesivePathIntersSimp3 [simp]: "segment A B \<Longrightarrow> length L \<ge> 1 \<Longrightarrow> \<not> lineCohesivePathInters (a # L) A B
    \<Longrightarrow> \<not> intersect ((a # L) ! i) ((a # L) ! Suc i) A B"
    apply (subgoal_tac "\<not> intersect a (hd L) A B")
    apply (induct L A B rule:lineCohesivePathInters.induct, simp, simp)
    apply (cases i, simp, simp)  
oops*)
(*lemma intersectNeg : "segment A B  \<Longrightarrow>
  \<not> lineCohesivePathInters L A B \<longrightarrow> \<not>(\<exists> i. intersect (L ! i) (L ! Suc i) A B)"
  apply (rule ccontr)
  apply (induct L A B rule:lineCohesivePathInters.induct) apply (safe)
  apply (auto) 
oops*)
lemma lineCohesivePathInters2: "segment A B \<Longrightarrow> length L \<ge> 2 \<Longrightarrow> (intersect (L ! i) (L ! Suc i) A B) \<Longrightarrow> lineCohesivePathInters L A B"
  apply (induct L A B rule:lineCohesivePathInters.induct)
  apply (auto)
  apply (subgoal_tac "intersect ((a # b # xs) ! i) ((b # xs) ! i) P R \<longleftrightarrow> lineCohesivePathInters (a # b # xs) P R")
  apply (auto)
  (*apply (cut_tac A=P and B=R and L="(b#xs)" in intersectNeg, auto)
by (metis nth_Cons')*)
sorry
(*lemma lineCohesivePathIntersSimp3 [simp]: "segment A B \<Longrightarrow> length xs \<ge> 1 \<Longrightarrow> intersect ((a # b # xs) ! i) ((a # b # xs) ! Suc i) A B \<Longrightarrow>
  \<not> lineCohesivePathInters (b # xs) A B \<Longrightarrow> lineCohesivePathInters [a,b] A B"
  apply (simp)
  apply (cut_tac A=A and B=B and a=a and b=b and L=xs and k=i in listIntersection, simp, simp)
  apply (simp) 
oops*)
theorem lineCohesivePathIntersEquiv : "segment A B \<Longrightarrow> length L \<ge> 2 \<Longrightarrow> lineCohesivePathInters L A B \<longleftrightarrow>
  (\<exists> i. intersect (L ! i) (L ! Suc i) A B)"
  by (auto simp add: lineCohesivePathInters1 lineCohesivePathInters2)


(*intersection(CohesivePath, CohesivePath)*)


(*move CohesivePath*)





end
