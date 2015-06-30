theory cyclePath
imports segmentList
begin

(*geschlossener Pfad*)
definition cyclePath :: "point2d list \<Rightarrow> point2d list" where
  "pointList P \<Longrightarrow> cyclePath P \<equiv> P @ [hd P]"
lemma [simp]: "pointList L \<Longrightarrow> hd L \<noteq> last L" by (cases L, auto simp add: pointList_def)
lemma [simp]: "pointList L \<Longrightarrow> length (cyclePath L) = length L + 1" by (simp add: cyclePath_def)
lemma [simp]: "pointList L \<Longrightarrow> hd(cyclePath L) = last(cyclePath L)" by (simp add: cyclePath_def hd_append)

(*alle benachbarten Kanten von cyclePath sind segmente*)
lemma cyclePathLastSegment : "pointList L \<Longrightarrow> segment (last L) (last (cyclePath L))"
  apply (simp add: cyclePath_def segment_def, subst neq_commute, simp)
done
theorem cyclePathSegments : "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> i < length P - 1 \<Longrightarrow> segment (P!i) (P! Suc i)"
  apply (unfold cyclePath_def, simp)
  apply (cut_tac L=L and a="hd L" in pointsSegmentsAppend1, simp)
  apply (simp add: segment_def, cases L, auto simp add: pointList_def)
done

(*zwei benachbarte Knoten im cyclePath sind ungleich*)
lemma cyclePathAdjacentSame: "pointList L \<Longrightarrow> i < length (cyclePath L) - 1 \<Longrightarrow> cyclePath L ! i \<noteq> cyclePath L ! Suc i"
  apply (cut_tac L=L and P= "cyclePath L" and i=i in cyclePathSegments, simp+)
  apply (simp add: segment_def)
done
lemma cyclePathAdjacentSame1 :"pointList L \<Longrightarrow> i < length (cyclePath L)  - 1 \<Longrightarrow> k < length (cyclePath L) - 1 \<Longrightarrow>
  cyclePath L ! i \<noteq> cyclePath L ! k \<Longrightarrow> cyclePath L ! Suc i \<noteq> cyclePath L ! Suc k"
sorry

(*keine 3 aufeinander folgenden Punkte im cyclePath sind collinear, wenn L collinear-frei ist*)
lemma cyclePathNotCollinear1:"pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow>
  a < length P - 2 \<Longrightarrow> signedArea (P ! a) (P ! Suc a) (P ! Suc (Suc a)) \<noteq> 0"
  apply (subgoal_tac "\<not> collinear (P! (length P - 3))(P!(length P - 2))(last P)")
    apply (simp)
    apply (simp add: cyclePath_def)
    apply (subgoal_tac "(L @ [hd L]) ! (length L - Suc 0) = L ! (length L - Suc 0)")
    apply (subgoal_tac "(L @ [hd L]) ! (length L - 2) = L ! (length L - 2)")
    apply (simp)
    apply (simp add: collinearList_def)
sorry
(*alle 3 aufeinander folgenden Ecken im cyclePath sind links oder rechts gerichtet; wenn L collinear-frei ist*)
theorem "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow>
  (\<forall> a < length P - 2. signedArea (P!a) (P ! Suc a) (P ! Suc(Suc a)) < 0)
  \<or> (\<forall> a < length P - 2. signedArea (P ! a) (P ! Suc a) (P ! Suc (Suc a)) > 0)"
  apply (safe del: allI)
  apply (simp)
  apply (simp add: collinearList_def)
oops
(*keine 3 Ecken im cyclePath sind collinear, ausgenommen letzer Knoten; wenn L collinear-frei ist*)
theorem cyclePathNotCollinear: "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow>
  P!a \<noteq> P!b \<and> P!a \<noteq> P!c \<and> P!c \<noteq> P!b \<Longrightarrow> \<not>collinear (P ! a) (P ! b) (P ! c)"
sorry
  
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
done thm lineCyclePathInters.cases
(*TODO: hier fehlt noch ein Beweis*)
lemma lineCyclePathInters2: "segment A B \<Longrightarrow> (\<exists> i. i < length L - 1 \<and> intersect (L ! i) (L ! Suc i) A B) \<Longrightarrow>
  lineCyclePathInters L A B"
sorry
theorem lineCyclePathIntersEq : "segment A B \<Longrightarrow> lineCyclePathInters L A B =
  (\<exists> i. i < length L - 1 \<and> intersect (L!i) (L ! Suc i) A B)"
  apply (rule iffI, metis lineCyclePathInters1)
  by(metis lineCyclePathInters2)


(*intersection(CyclePath, CyclePath)*)






end
