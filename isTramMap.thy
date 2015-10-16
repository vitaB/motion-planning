theory isTramMap
imports trapezoidalMap
begin


(*Definition für trapMap*)
definition NoIntersectInTramMap :: "tDag \<Rightarrow> bool" where
  "NoIntersectInTramMap D \<equiv> \<forall> A B. (A \<in> set (yDagList D) \<and> B \<in> set (yDagList D)) \<longrightarrow> 
  \<not>intersect (fst A) (snd A) (fst B) (snd B)"
definition isTramMap :: "tDag \<Rightarrow> bool" where
  "isTramMap D \<equiv> trapezList (tDagList D) \<and> pointsInTramMap D
  \<and> trapezodalMapNeighbor D \<and> uniqueXCoord (xDagList D) \<and> NoIntersectInTramMap D"

lemma isTramMapRBox[simp]: "isTrapez X \<Longrightarrow> isTramMap (Tip X)"
  apply (auto simp add: isTramMap_def pointInDag_def pointInTrapez_def trapezList_def)
by (auto simp add: pointsInTramMap_def NoIntersectInTramMap_def)
  


(*definition für komp. segment mit einer Trap-Map*)
definition segmentXNode :: "tDag \<Rightarrow> point2d \<Rightarrow> bool" where
  "segmentXNode D P \<equiv> \<forall> a. a \<in> set (xDagList D) \<and> a \<noteq> P \<longrightarrow> xCoord a \<noteq> xCoord P"
lemma segmentAndDagUnicX[simp]:"segmentXNode D P \<Longrightarrow> P \<notin> set (xDagList D) \<Longrightarrow>
  uniqueXCoord (xDagList D @ [P])"
  apply (auto simp add: segmentXNode_def)
  apply (case_tac "\<exists> a. a \<in> set (xDagList D)", erule exE)
  apply (erule_tac x=a in allE, simp, safe)
sorry

definition segmentCompWithDag :: "tDag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<equiv> leftFrom P Q \<and> pointInDag D P \<and> pointInDag D Q
  \<and> segmentXNode D P \<and> segmentXNode D Q
  \<and> (\<forall> A. A \<in> set (yDagList D) \<longrightarrow> \<not>intersect (fst A) (snd A) P Q)"
lemma segmentCompWithDagSym[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  \<forall> A. A \<in> set (yDagList D) \<longrightarrow> \<not>intersect P Q (fst A) (snd A)"
  apply (auto simp add: segmentCompWithDag_def)
  apply (erule_tac x=a in allE, erule_tac x=b in allE, simp)
by (metis NotIntersectSym)
  
lemma segmentAndDagUnicX1[simp]:"isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  P \<notin> set (xDagList D) \<Longrightarrow> Q \<notin> set (xDagList D) \<Longrightarrow> uniqueXCoord (xDagList D @ [P, Q])"
sorry

lemma pointNotXNode: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  \<forall> T. T \<in> set (tDagList D) \<longrightarrow> rightP T \<noteq> P \<and> leftP T \<noteq> P \<Longrightarrow> P \<notin> set (xDagList D)"
sorry



(*##############NoIntersectInTramMap###############*)

lemma replaceTipNoIntersect[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  NoIntersectInTramMap (replaceTip oT (newDag D T TM P Q) D)"
  apply (auto simp add: NoIntersectInTramMap_def)
  apply (insert replaceTipYDagList1, atomize)
  apply (erule_tac x="(a, b)" in allE, erule_tac x=oT in allE,
    erule_tac x="newDag D T TM P Q" in allE, erule_tac x=D in allE)
  apply (insert replaceTipYDagList1, atomize)
  apply (erule_tac x="(aa, ba)" in allE, erule_tac x=oT in allE,
    erule_tac x="newDag D T TM P Q" in allE, erule_tac x=D in allE, auto)
  apply (simp add: NoIntersectInTramMap_def isTramMap_def)
  using segmentCompWithDag_def apply auto[1]
by (meson BNF_Greatest_Fixpoint.subst_Pair segmentCompWithDagSym)

lemma addSegmentNoIntersect: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  NoIntersectInTramMap (addSegmentToTrapezoidalMap D P Q)"
  apply (simp add: addSegmentToTrapezoidalMap_def)
by (metis NoIntersectInTramMap_def NotIntersectSym fstI isTramMap_def notIntersectSame
  replaceYDagListElem segmentCompWithDag_def sndI)


(*##############trapezList###############*)
lemma newTrapezPointsXOrder1[simp]: "isTrapez T \<Longrightarrow> pointInTrapez T P \<Longrightarrow> pointInTrapez T Q \<Longrightarrow>
  leftFrom P Q \<Longrightarrow> trapezPointsXOrder (Abs_trapez (topT T, (P, Q), P, Q))"
  apply (auto simp add: trapezPointsXOrder_def)
  using isTrapez_def trapezPointsXOrder_def apply blast
by (simp add: isTrapez_def leftP_def pointInTrapez_def trapezPointsXOrder_def xCoord_def)+

lemma newTrapezA[simp]: "isTrapez T \<Longrightarrow> pointInTrapez T P \<Longrightarrow> pointInTrapez T Q \<Longrightarrow> leftFrom P Q \<Longrightarrow>
  trapezList (tDagList(newDagSimpA T P Q))"
  apply (simp add: newDagSimpA_def trapezList_def, auto)
  apply (auto simp add: isTrapez_def)
sorry
lemma addSegmentTrapezList: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow> trapezList (tDagList (addSegmentToTrapezoidalMap D P Q))"
sorry



(*##############pointsInTramMap###############*)
lemma newDagPointInTrapez: "D = (Node (Tip (Abs_trapez (topT T, (P, Q), P, Q))) (yNode (P, Q))
  (Tip (Abs_trapez ((P, Q), bottomT T, P, Q)))) \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D a \<Longrightarrow>
  leftTurn P Q a \<Longrightarrow> trapezList (tDagList D) \<Longrightarrow> pointInTrapez (Abs_trapez (topT T, (P, Q), P, Q)) a"
  apply (auto simp add: pointInDag_def)
  apply (cut_tac T="(Abs_trapez ((P, Q), bottomT T, P, Q))" and P=a in isNotInTrapez)
by (auto simp add: trapezListSimp)
  

lemma addSegmentPointsInTramMap: "isTrapez T \<Longrightarrow> pointInTrapez T P \<Longrightarrow> pointInTrapez T Q \<Longrightarrow>
  pointsInTramMap (newDagSimpA T P Q)"
  apply (auto simp add: newDagSimpA_def pointsInTramMap_def)
  apply (subgoal_tac "isTrapez (Abs_trapez (topT T, (P, Q), P, Q))")
  apply (metis bottomT leftP leftPRigthFromRightP1 leftRightTurn newDagPointInTrapez newDagSimpA_def
    newTrapezA snd_conv)
oops

lemma addSegmentPointsInTramMap: "isTrapez T \<Longrightarrow> pointInTrapez T P \<Longrightarrow> pointInTrapez T Q \<Longrightarrow>
  pointsInTramMap (newDagSimp T P Q)"
  apply (simp add: newDagSimp_def)
oops
lemma addSegmentPointsInTramMap: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow> pointsInTramMap (addSegmentToTrapezoidalMap D P Q)"
  apply (simp add: addSegmentToTrapezoidalMap_def)
sorry






(*##############uniqueXCoord for xDagList ###############*)
lemma newDagSimpLeftCorner[simp]:"leftFrom P Q \<Longrightarrow> leftP T = P \<Longrightarrow>
  a \<in> set (xDagList (newDagSimp T P Q)) \<Longrightarrow> a \<noteq> P"
  apply (auto simp add: newDagSimp_def)
  apply (case_tac "rightP T \<noteq> Q ")
    apply (simp add: newDagSimpQ_def newDagSimpA_def, blast)
by (auto simp add: newDagSimpA_def)
lemma newDagSimpRightCorner[simp]:"leftFrom P Q \<Longrightarrow> rightP T = Q \<Longrightarrow>
  a \<in> set (xDagList (newDagSimp T P Q)) \<Longrightarrow> a \<noteq> Q"
  apply (auto simp add: newDagSimp_def)
  apply (case_tac "leftP T \<noteq> P ")
    apply (simp add: newDagSimpQ_def newDagSimpA_def, blast)
by (auto simp add: newDagSimpA_def)
lemma newDagLeftCorner[simp]:"leftFrom P Q \<Longrightarrow> leftP T = P \<Longrightarrow>
  a \<in> set (xDagList (newDag D T TM P Q)) \<Longrightarrow> a \<noteq> P"
  apply (auto simp add: newDag_def)
  apply (case_tac "length TM = Suc 0", simp)
    using newDagSimpLeftCorner apply blast
  apply (case_tac "queryTrapezoidMap D (leftP T) = T")
    apply (auto simp add: newDagFirst_def newDagFirstY_def)
  apply (case_tac "queryTrapezoidMap D Q = T \<or> rightP T = Q")
    apply (auto simp add: newDagLast_def newDagLastY_def)
  apply (case_tac "rightP (queryTrapezoidMap D Q) = Q")
    apply (simp add: newDagLastY_def)
  apply (simp, safe, metis)
by (simp add: newDagLastY_def)
lemma newDagRightCorner[simp]:"leftFrom P Q \<Longrightarrow> rightP T = Q \<Longrightarrow>
  a \<in> set (xDagList (newDag D T TM P Q)) \<Longrightarrow> a \<noteq> Q"
  apply (auto simp add: newDag_def)
  apply (case_tac "length TM = Suc 0", simp)
    using newDagSimpRightCorner apply blast
  apply (simp)
  apply (case_tac "queryTrapezoidMap D P = T", simp)
    apply (subgoal_tac "xDagList (newDagFirst T TM P (rightP T)) = [P]
      \<or> xDagList (newDagFirst T TM P (rightP T)) = []")
    apply (metis empty_iff insert_iff list.set(1) list.set(2) pointsUniqueXCoord uniqueX_notIn)
    using xDagListNewDagFirst apply blast
  apply (case_tac "queryTrapezoidMap D (rightP T) = T")
    apply (auto simp add: newDagLast_def newDagLastY_def)
done


lemma replaceTipElement[intro]:"a \<in> set (xDagList (replaceTip T (newDag D T TM P Q) D)) \<Longrightarrow>
  a \<in> set (xDagList D) \<or> a \<in> set [P,Q]"
  apply (cut_tac oT=T and nT="newDag D T TM P Q" and D=D and a=a in replaceTipXDagList1, assumption)
  apply (erule disjE, simp)
  apply (thin_tac "a \<in> set (xDagList (replaceTip T (newDag D T TM P Q) D))")
by (metis insert_iff list.set(2) xDagListNewDag)
   

lemma "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow> leftP T = P \<Longrightarrow>
   List.count (xDagList (replaceTip T (newDag D T TM P Q) D)) P \<le> 1"
  apply (case_tac "\<exists> a. a \<in> set (xDagList (replaceTip T (newDag D T TM P Q) D))")
  apply (erule exE)
  apply (subgoal_tac "\<forall> a. a \<in> set (xDagList (replaceTip T (newDag D T TM P Q) D)) \<longrightarrow>
         a \<in> set (xDagList D) \<or> a \<in> set (xDagList (newDag D T TM P Q))")
  apply (auto)
  apply (subgoal_tac "xDagList (newDag D T TM (leftP T) Q) = [Q] \<or>
    xDagList (newDag D T TM (leftP T) Q) = []")
  apply (auto)
  apply (subgoal_tac "Q \<noteq> P")
  apply (subgoal_tac "List.count (xDagList D) (leftP T) \<le> Suc 0")
  apply (erule_tac x=a in allE, simp)
  defer
  using isTramMap_def uniqueXNotDouble apply auto[1]
sorry
lemma bar1:"isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow> rightP T = Q \<Longrightarrow>
   List.count (xDagList (replaceTip T (newDag D T TM P Q) D)) Q \<le> 1"
sorry

lemma foo2:"isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow>
  List.count (xDagList (replaceDag D (intersectedTrapez D P Q) TM P Q)) Q = 1"
  apply (subgoal_tac "\<not>(\<exists> i. i < length (intersectedTrapez D P Q) - 1 \<and> i \<noteq> 0
    \<and> rightP ((intersectedTrapez D P Q)!i) = Q)")
  apply (subgoal_tac "\<not>(\<exists> i. i < length (intersectedTrapez D P Q) \<and> i \<noteq> 0
    \<and> leftP ((intersectedTrapez D P Q)!i) = P)")
  apply (induct D "intersectedTrapez D P Q" TM P Q rule: replaceDag.induct)
  apply (simp del: newDagSimpRightCorner newDagSimpLeftCorner)
  apply (metis (mono_tags) followSegment.simps intersectedTrapez_def isTramMap_def
    list.sel(2) list.sel(3) not_Cons_self2)
  apply (simp del: newDagSimpRightCorner newDagSimpLeftCorner)
  
sorry
lemma foo3:"isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow>
  List.count (xDagList (replaceDag D (intersectedTrapez D P Q) TM P Q)) P = 1"
sorry

lemma addSegmentsUnicX: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow> uniqueXCoord (xDagList (addSegmentToTrapezoidalMap D P Q))"
  (*nur da erste Trapez kann P entrhalten und das letzte Trapez Q,
    die mittleren Trapeze enthalten nichts*)
  apply (simp add: addSegmentToTrapezoidalMap_def)
  apply (subgoal_tac "\<forall> (a::point2d). List.count
    (xDagList (replaceDag D (intersectedTrapez D P Q) (intersectedTrapez D P Q) P Q)) a \<le> 1")
  
  apply (auto)
  apply (subgoal_tac "\<exists> a. a \<in> set
    (xDagList (replaceDag D (intersectedTrapez D P Q) (intersectedTrapez D P Q) P Q))", erule exE)
  apply (cut_tac TM= "(intersectedTrapez D P Q)" and TN="(intersectedTrapez D P Q)" and D=D
    and a=a and P=P and Q=Q in replaceXDagListElem, simp)
  apply (erule_tac x=a in allE)
oops





(*####################*)


lemma "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow> D = addSegmentToTrapezoidalMap D P Q \<Longrightarrow>
  P \<in> set (xDagList D) \<and> Q \<in> set (xDagList D)"
oops
lemma addSegmentPointsInMap: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow> pointsInTramMap (addSegmentToTrapezoidalMap D P Q)"
  apply (simp add: addSegmentToTrapezoidalMap_def)
oops

theorem "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow> isTramMap (addSegmentToTrapezoidalMap D P Q)"
  apply (simp add: addSegmentToTrapezoidalMap_def)
oops



end