theory cyclePath
imports segmentList
begin

(*geschlossener Pfad*)
definition cyclePath :: "point2d list \<Rightarrow> point2d list" where
  "pointList P \<Longrightarrow> cyclePath P \<equiv> P @ [hd P]"
lemma [simp]: "pointList L \<Longrightarrow> hd L \<noteq> last L" by (cases L, auto simp add: pointList_def)
lemma [simp]: "pointList L \<Longrightarrow> length (cyclePath L) = length L + 1" by (simp add: cyclePath_def)
lemma [simp]: "pointList L \<Longrightarrow> hd(cyclePath L) = last(cyclePath L)" by (simp add: cyclePath_def hd_append)

(*Kreis rückwärts ausgeben*)
definition revCycle :: "point2d list \<Rightarrow> point2d list" where
  "pointList L \<Longrightarrow> revCycle L \<equiv> cyclePath (hd L # rev (tl L))"
lemma [simp]: "pointList L \<Longrightarrow> pointList (hd L # rev (tl L))"
  apply (simp add: pointList_def, safe, simp)
  apply (metis distinct.simps(2) empty_iff eq_numeral_simps(4) list.collapse list.set(1) nth_Cons_numeral nth_equal_first_eq)
  apply (simp add: distinct_tl)
done
lemma revCycleEq [simp]: "pointList L \<Longrightarrow> revCycle L = rev (cyclePath L)"
  apply (simp add: revCycle_def cyclePath_def)
  apply (metis list.collapse list.size(3) not_less numeral_eq_Suc pointList_def rev.simps(2) zero_less_Suc)
done
(*der Allgemeinfall mit ~~/src/HOL/Library/Permutation ist evtl. einfacher*)
lemma revCycleCollinear [simp]: "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> \<not>collinearList (hd L # rev (tl L))"
  apply (simp add: collinearList_def, safe)
  apply (erule_tac x=a in allE, safe, simp)
  apply (erule_tac x=b in allE, safe, simp)
  apply (erule_tac x=c in allE, safe)
  apply (simp)
sorry

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

(*keine 3 aufeinander folgenden Punkte im cyclePath L sind collinear, wenn L collinear-frei ist*)
lemma cyclePathNotCollinear1:"pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow>
  a < length P - 2 \<Longrightarrow> signedArea (P ! a) (P ! Suc a) (P ! Suc (Suc a)) \<noteq> 0"
  (*Beweis braucht zu lange: apply (subgoal_tac "(a = length P - 3 \<longrightarrow> \<not> collinear (P! a)(P!Suc a)(last P)) \<and>
    (a < length P - 3 \<longrightarrow> signedArea (P ! a) (P ! Suc a) (P ! Suc (Suc a)) \<noteq> 0) ")
    apply (simp only: colliniearRight )
    apply (metis Suc_1 Suc_lessI diff_Suc_1 diff_Suc_eq_diff_pred diff_less_Suc diff_self_eq_0 last_conv_nth length_greater_0_conv numeral_3_eq_3 zero_less_diff)
  apply (safe)
  apply (simp add: cyclePath_def collinearList_def)
  apply (erule_tac x=0 in allE, safe, simp)
  apply (erule_tac x="(length L - 2)" in allE, safe, simp)
  apply (erule_tac x="Suc (length L - 2)" in allE, safe, simp)
  apply (smt2 One_nat_def Suc_1 Suc_diff_1 Suc_diff_Suc le_refl length_greater_0_conv list.size(3) not_less_eq_eq not_less_iff_gr_or_eq numeral_eq_Suc pointList_def pred_numeral_simps(3) zero_less_diff)
  apply (simp)
(*hä?*)
  apply (metis One_nat_def Suc_eq_plus1 Suc_lessD hd_conv_nth length_0_conv less_diff_conv less_nat_zero_code nth_append)
  apply (simp add: cyclePath_def collinearList_def)
  apply (erule_tac x=a in allE, safe, simp)
  apply (erule_tac x="Suc a" in allE, safe, simp)
  apply (erule_tac x="Suc (Suc a)" in allE, safe, simp)
  apply (simp, simp, simp)
  apply(smt2 One_nat_def Suc_eq_plus1 Suc_lessD add_Suc_right colliniearRight less_diff_conv nth_append numeral_2_eq_2)
done*)sorry
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
