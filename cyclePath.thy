theory cyclePath
imports segmentList
begin

(*closed path*)
definition cyclePath :: "point2d list \<Rightarrow> point2d list" where
  "pointList P \<Longrightarrow> cyclePath P \<equiv> P @ [hd P]"
lemma cyclePathHd [simp]: "pointList L \<Longrightarrow> hd L \<noteq> last L"by (cases L, auto simp add: pointList_def)
lemma cyclePathLength [simp]: "pointList L \<Longrightarrow> length (cyclePath L) = length L + 1"
  by (simp add: cyclePath_def)
lemma cyclePathHd1 [simp]: "pointList L \<Longrightarrow> hd(cyclePath L) = last(cyclePath L)"
  by (simp add: cyclePath_def hd_append)


(*Output cycle in reverse*)
definition revCycle :: "point2d list \<Rightarrow> point2d list" where
  "pointList L \<Longrightarrow> revCycle L \<equiv> cyclePath (hd L # rev (tl L))"
lemma [simp]: "pointList L \<Longrightarrow> pointList (hd L # rev (tl L))"
  apply (simp add: pointList_def, safe, simp)
  apply (metis distinct.simps(2) empty_iff eq_numeral_simps(4) list.collapse list.set(1)
    nth_Cons_numeral nth_equal_first_eq)
by (simp add: distinct_tl)
lemma revCycleEq [simp]: "pointList L \<Longrightarrow> revCycle L = rev (cyclePath L)"
  apply (simp add: revCycle_def cyclePath_def)
by (metis list.collapse list.size(3) not_less numeral_eq_Suc pointList_def rev.simps(2)
    zero_less_Suc)
(*der Allgemeinfall mit ~~/src/HOL/Library/Permutation ist evtl. einfacher*)
lemma revCycleCollinear [simp]: "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow>
    \<not>collinearList (hd L # rev (tl L))"
  apply (simp add: collinearList_def, safe)
  apply (erule_tac x=a in allE, safe, simp)
  apply (erule_tac x=b in allE, safe, simp)
  apply (erule_tac x=c in allE, safe)
  apply (simp)
sorry

(*all adjacent edges of cyclePath are segments*)
lemma cyclePathLastSegment : "pointList L \<Longrightarrow> segment (last L) (last (cyclePath L))"
  by (simp add: cyclePath_def segment_def, subst neq_commute, simp)
theorem cyclePathSegments : "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> i < length P - 1 \<Longrightarrow>
  segment (P!i) (P! Suc i)"
  apply (unfold cyclePath_def, simp, cut_tac L=L and a="hd L" in pointsSegmentsAppend1, simp)
by (simp add: segment_def, cases L, auto simp add: pointList_def)

(*two adjacent nodes in cyclepath are unequal*)
lemma cyclePathAdjacentSame: "pointList L \<Longrightarrow> i < length (cyclePath L) - 1 \<Longrightarrow>
    cyclePath L ! i \<noteq> cyclePath L ! Suc i"
  apply (cut_tac L=L and P= "cyclePath L" and i=i in cyclePathSegments, simp+)
  apply (simp add: segment_def)
done
lemma cyclePathAdjacentSame1: "pointList L \<Longrightarrow> i < length (cyclePath L) - 1 \<Longrightarrow>
    k < length (cyclePath L) - 1 \<Longrightarrow> cyclePath L ! i \<noteq> cyclePath L ! k \<Longrightarrow>
    cyclePath L ! Suc i \<noteq> cyclePath L ! Suc k"
    apply (rule ccontr, simp)
by (smt Cons_nth_drop_Suc Suc_lessI cyclePath_def diff_Suc_1 hd_append hd_drop_conv_nth
  id_take_nth_drop nat.distinct(1) nth_append nth_append_length nth_eq_iff_index_eq pointList_def
  take_0 zero_less_Suc)

(*no 3 consecutive points in cyclepath L are collinear if L is collinear-free*)
lemma cyclePathNotCollinear1:"pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow>
  a < length P - 2 \<Longrightarrow> signedArea (P ! a) (P ! Suc a) (P ! Suc (Suc a)) \<noteq> 0"
  apply (subgoal_tac "(a = length P - 3 \<longrightarrow> \<not> collinear (P! a)(P!Suc a)(last P)) \<and>
    (a < length P - 3 \<longrightarrow> signedArea (P ! a) (P ! Suc a) (P ! Suc (Suc a)) \<noteq> 0) ")
  apply (simp only: colliniearRight)
   apply (smt Suc_diff_Suc Suc_eq_plus1 add_2_eq_Suc' colliniearRight diff_Suc_1 last_conv_nth
     diff_Suc_eq_diff_pred gr_implies_not0  length_0_conv less_SucE less_diff_conv less_imp_Suc_add
     less_trans_Suc numeral_2_eq_2 numeral_3_eq_3 zero_less_Suc)
  apply (safe)
  apply (simp add: cyclePath_def collinearList_def)
  apply (erule_tac x=0 in allE, safe, simp)
  apply (erule_tac x="(length L - 2)" in allE, safe, simp)
  apply (erule_tac x="Suc (length L - 2)" in allE, safe, simp)
  apply (smt One_nat_def Suc_1 Suc_diff_1 Suc_diff_Suc le_refl length_greater_0_conv list.size(3)
    not_less_eq_eq not_less_iff_gr_or_eq numeral_eq_Suc pointList_def pred_numeral_simps(3) zero_less_diff)
  apply (simp)
  apply (metis One_nat_def Suc_eq_plus1 Suc_lessD hd_conv_nth length_0_conv less_diff_conv
    less_nat_zero_code nth_append)
  apply (simp add: cyclePath_def collinearList_def)
  apply (erule_tac x=a in allE, safe, simp)
  apply (erule_tac x="Suc a" in allE, safe, simp)
  apply (erule_tac x="Suc (Suc a)" in allE, safe, simp)
  apply (simp, simp, simp)
by(smt One_nat_def Suc_eq_plus1 Suc_lessD add_Suc_right colliniearRight less_diff_conv
    nth_append numeral_2_eq_2)

(*all consecutive 3 corners in cyclepath are left or right oriented; if L is collinear-free*)
theorem cyclePathNotCollinear2: "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow>
  a < length P - 2 \<Longrightarrow> (signedArea (P!a) (P ! Suc a) (P ! Suc(Suc a)) < 0)
  \<or> ( signedArea (P ! a) (P ! Suc a) (P ! Suc (Suc a)) > 0)"
  apply (safe del: allI)
  apply (simp)
  apply (simp add: collinearList_def)
  apply (case_tac "a < length P - 3", simp)
    apply (subgoal_tac "signedArea (cyclePath L ! a) (cyclePath L ! Suc a)
      (cyclePath L ! Suc (Suc a)) = signedArea (L ! a) (L ! Suc a) (L ! Suc (Suc a))")
    apply (smt collinearListAdj collinearList_def colliniearRight)
    apply (simp add: cyclePath_def)
    apply (smt Suc_diff_Suc Suc_less_SucD Suc_mono diff_Suc_less diff_less_Suc less_trans_Suc nth_append numeral_2_eq_2 zero_less_diff)
  apply (simp)
  apply (case_tac "a = length L - 2", auto simp add: cyclePath_def)
  apply (subgoal_tac "signedArea ((L @ [hd L]) ! (length L - 2)) ((L @ [hd L]) ! Suc (length L - 2))
     ((L @ [hd L]) ! Suc (Suc (length L - 2))) \<noteq> 0", simp)
using collinearList_def cyclePathNotCollinear1 cyclePath_def less_imp_Suc_add by auto

(*no 3 corners in cyclepath are collinear, except Last node; if L is collinear-free*)
theorem cyclePathNotCollinear: "pointList L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> P = cyclePath L \<Longrightarrow>
  a < length P \<Longrightarrow> b < length P \<Longrightarrow> c < length P \<Longrightarrow>
  P!a \<noteq> P!b \<and> P!a \<noteq> P!c \<and> P!c \<noteq> P!b \<Longrightarrow> \<not>collinear (P ! a) (P ! b) (P ! c)"
by (smt Cons_nth_drop_Suc collRotate collinearList_def cyclePath_def diff_Suc_1 hd_append
  hd_drop_conv_nth id_take_nth_drop last_conv_nth last_snoc length_append_singleton nth_append
  length_greater_0_conv less_antisym less_imp_Suc_add less_nat_zero_code list.size(3) take_0)

  
(*intersection(cyclePath, Strecke A B)*)
fun lineCyclePathInters :: "point2d list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "lineCyclePathInters [] P R = False"
| "lineCyclePathInters [a] P R = False"
| "lineCyclePathInters (a#b#xs) P R = (intersect a b P R \<or> lineCyclePathInters (b#xs) P R)"
(*some simple Lemmas. Simplifies proofs*)
lemma lineCyclePathIntersSimp [simp]: "\<not>lineCyclePathInters (b#L) A B \<Longrightarrow>
    lineCyclePathInters (a#b#L) A B = lineCyclePathInters [a,b] A B"
  by (simp)
lemma lineCyclePathIntersSimp1 [simp]: "length L \<ge> 1 \<Longrightarrow> \<not>lineCyclePathInters (b#L) A B \<Longrightarrow>
    \<not>intersect b (hd L) A B"
  by (cases L, auto)
lemma lineCyclePathIntersSimp2 [simp]: "\<not>lineCyclePathInters [a,b] A B \<Longrightarrow>
    lineCyclePathInters (a#b#L) A B = lineCyclePathInters (b#L) A B"
  by (simp)
lemma lineCyclePathIntersSimp6 : " \<not>lineCyclePathInters (b # xs) P R
  \<Longrightarrow> \<exists> i < length (a # b # xs) - 1. intersect P R ((a # b # xs) ! i) ((a # b # xs) ! Suc i) \<Longrightarrow> intersect P R a b"
  apply (induct "(b # xs)" P R rule: lineCyclePathInters.induct, auto)
  apply (subgoal_tac "i=0", simp)
  apply (rule ccontr, simp)
oops
lemma lineCyclePathIntersSimp3 : "i < length (a # b # xs) - 1 \<Longrightarrow> \<not>lineCyclePathInters (b # xs) P R
  \<Longrightarrow> intersect P R ((a # b # xs) ! i) ((a # b # xs) ! Suc i) \<Longrightarrow> intersect P R a b"
  apply (simp)
  apply (subgoal_tac "\<not>intersect P R ((b # xs) ! i) ((xs) ! i)", auto)
oops
lemma lineCyclePathIntersNeg : "\<not>lineCyclePathInters (a#b#L) A B \<Longrightarrow>
    \<not>lineCyclePathInters [a,b] A B \<and> \<not>lineCyclePathInters (b#L) A B"
  by (simp)

(*when there is an intersection between cyclepath and segment AB?*)
lemma lineCyclePathInters1: "lineCyclePathInters L A B \<Longrightarrow>
  (\<exists> i. i<length L - 1 \<and> intersect (L!i) (L ! Suc i) A B)"
  apply (induct L A B rule:lineCyclePathInters.induct, simp, simp)
by (auto, rule_tac x="i + 1" in exI, simp)
(*TODO: hier fehlt noch ein Beweis*)
lemma lineCyclePathInters2: "(\<exists> i. i < length L - 1 \<and> intersect (L ! i) (L ! Suc i) A B) \<Longrightarrow>
  segment A B \<Longrightarrow> lineCyclePathInters L A B"
  apply (induction rule: lineCyclePathInters.induct, auto)
by (metis Suc_eq_plus1 Suc_less_eq Suc_pred add.left_neutral neq0_conv nth_Cons')

theorem lineCyclePathIntersEq: "segment A B \<Longrightarrow> lineCyclePathInters L A B =
  (\<exists> i. i < length L - 1 \<and> intersect (L!i) (L ! Suc i) A B)"
  apply (rule iffI, metis lineCyclePathInters1)
by(metis lineCyclePathInters2)


(*intersection(CyclePath, CyclePath)*)
definition cyclePathIntersect ::  "point2d list \<Rightarrow> point2d list \<Rightarrow> bool" where
  "cyclePathIntersect A B \<equiv> \<exists> i < length B - 1. lineCyclePathInters A (B!i) (B!Suc i)"
lemma cyclePathNotIntersectSame: "pointList P \<Longrightarrow> A = cyclePath P \<Longrightarrow> intersectionFreePList A \<Longrightarrow>
  cyclePathIntersect A A \<Longrightarrow> False"
  apply (auto simp add: cyclePathIntersect_def)
  apply (case_tac "(A, (A!0), (A!Suc 0))" rule: lineCyclePathInters.cases)
  apply (simp add: cyclePath_def)
  using cyclePath_def apply auto[1]
  apply (simp,safe, simp add: pointList_def)
  apply (subgoal_tac "segment a b \<and> segment ((a # b # xs) ! i) ((b # xs) ! i)", simp add: intersect_def)
oops

lemma cyclePathIntersectSym: "pointList P \<Longrightarrow> pointList Q \<Longrightarrow> A = cyclePath P \<Longrightarrow> B = cyclePath Q\<Longrightarrow> 
  cyclePathIntersect A B = cyclePathIntersect B A"
  apply (auto simp add: cyclePathIntersect_def)
  apply (case_tac "(A, (B ! i), (B ! Suc i))" rule: lineCyclePathInters.cases,safe)
  apply (simp+, safe)
  apply (rule_tac x=0 in exI, safe, simp add: pointList_def, simp)
  apply (metis cyclePathSegments cyclePath_def diff_Suc_1 impossible_Cons intersectSym1 length_Cons
     le0 length_append_singleton lineCyclePathInters2 list.sel(3) neq0_conv nth_Cons_0 nth_tl)
  apply (smt Suc_mono cyclePathSegments cyclePath_def diff_Suc_1 intersectSym1 length_Cons nth_tl
    length_append_singleton less_SucI lineCyclePathInters1 lineCyclePathInters2 list.sel(3))
by (metis add_diff_cancel_right' cyclePathLength cyclePathSegments intersectSym1 lineCyclePathInters1 lineCyclePathInters2)



(*at least one of cyclepaths intersected*)
definition cyclePathsIntersect :: "(point2d list) list \<Rightarrow> bool" where
  "pointLists PL \<Longrightarrow> cyclePathsIntersect PL \<equiv> \<exists> i j. i\<noteq>j \<and> i < length PL \<and> j < length PL
    \<and> cyclePathIntersect (cyclePath (PL!i)) (cyclePath (PL!j))"
lemma cyclePathsIntersectSimp: "pointList P \<Longrightarrow> pointList Q \<Longrightarrow>
  cyclePathIntersect (cyclePath P) (cyclePath Q) = cyclePathsIntersect [P , Q]"
  apply (subgoal_tac "pointLists [P, Q]")
  apply (simp only: cyclePathsIntersect_def, safe) defer
  apply (simp, case_tac i, simp)
  apply (smt One_nat_def Suc_1 cyclePathIntersect_def cyclePathSegments intersectSym1 less_2_cases
    lineCyclePathIntersEq nth_Cons' nth_Cons_Suc)
  using pointListsSimp apply blast
by (rule_tac x=0 in exI, rule_tac x=1 in exI, auto)


end