theory isTramMap
imports trapezoidalMap
begin


(*Definition für trapMap*)
definition vertexInTramMap :: "tDag \<Rightarrow> bool" where
  "vertexInTramMap D \<equiv> \<forall> T \<in> set (tDagList D). \<forall> P \<in> set (xDagList D).
  pointInTrapez T P \<longrightarrow> leftP T = P \<or> rightP T = P"
definition NoIntersectInTramMap :: "tDag \<Rightarrow> bool" where
  "NoIntersectInTramMap D \<equiv> \<forall> A B. A \<in> set (yDagList D) \<and> B \<in> set (yDagList D) \<longrightarrow> 
  \<not>intersect (fst A) (snd A) (fst B) (snd B)"
definition isTramMap :: "tDag \<Rightarrow> bool" where
  "isTramMap D \<equiv> trapezList (tDagList D) \<and> pointsInTramMap D \<and> vertexInTramMap D
  \<and> trapezodalMapNeighbor D \<and> uniqueXCoord (xDagList D) \<and> NoIntersectInTramMap D"

lemma isTramMapRBox[simp]: "isTrapez X \<Longrightarrow> isTramMap (Tip X)"
  apply (auto simp add: isTramMap_def pointInDag_def pointInTrapez_def trapezList_def)
by (auto simp add: pointsInTramMap_def vertexInTramMap_def NoIntersectInTramMap_def)


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
  \<and> (\<forall> A \<in> set (yDagList D). \<not>intersect (fst A) (snd A) P Q)"
lemma segmentAndDagUnicX1[simp]:"isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  P \<notin> set (xDagList D) \<Longrightarrow> Q \<notin> set (xDagList D) \<Longrightarrow> uniqueXCoord (xDagList D @ [P, Q])"
sorry


lemma segmentCompWithDag:"isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow> P \<noteq> Q"
  by (auto simp add: segmentCompWithDag_def)
  
  
lemma pointNotXNode: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  \<forall> T. T \<in> set (tDagList D) \<and> rightP T \<noteq> P \<and> leftP T \<noteq> P \<Longrightarrow> P \<notin> set (xDagList D)"
sorry

lemma addSegmentTrapezList: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow> trapezList (tDagList (addSegmentToTrapezoidalMap D P Q))"
sorry


lemma uniqueXInNewDagSimp[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  T \<in> set (tDagList D) \<Longrightarrow> uniqueXCoord (xDagList D @ xDagList (newDagSimp T P Q))"
  apply (auto simp add: newDagSimp_def newDagSimpQ_def newDagSimpA_def isTramMap_def)
  apply (subgoal_tac "rightP T \<noteq> P \<and> leftP T \<noteq> Q")
sorry


lemma uniqueXInNewDagFirst[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  T \<in> set (tDagList D) \<Longrightarrow> uniqueXCoord (xDagList D @ xDagList (newDagFirst a TM P Q))"
  apply (auto simp add: newDagFirst_def newDagFirstY_def isTramMap_def)
sorry
lemma uniqueXInNewDagLast[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  T \<in> set (tDagList D) \<Longrightarrow> uniqueXCoord (xDagList D @ xDagList (newDagLast a TM P Q))"
  apply (auto simp add: newDagLast_def newDagLastY_def isTramMap_def)
sorry
lemma uniqueXInNewDagM[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  T \<in> set (tDagList D) \<Longrightarrow> uniqueXCoord (xDagList D @ xDagList (newDagM a TM P Q))"
    by (auto simp add: newDagM_def isTramMap_def)                                           
lemma uniqueXInNewDag[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  T \<in> set (tDagList D) \<Longrightarrow> uniqueXCoord (xDagList D @ xDagList (newDag D T TM P Q))"
  by (auto simp add: newDag_def isTramMap_def)



lemma replaceTipElement[intro]:"isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  a \<in> set (xDagList (replaceTip T (newDag D T TM P Q) D)) \<Longrightarrow> a \<in> set (xDagList D) \<or> a \<in> set [P,Q]"
  apply (cut_tac oT=T and nT="newDag D T TM P Q" and D=D and a=a in replaceTipXDagList1, assumption)
  apply (erule disjE, simp)
  apply (thin_tac "a \<in> set (xDagList (replaceTip T (newDag D T TM P Q) D))")
by (metis insert_iff list.set(2) xDagListNewDag)
(*lemma replaceTipDistinct[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow> T \<in> set (tDagList D)
  \<Longrightarrow> distinct (xDagList (replaceTip T (newDag D T TM P Q) D))"
  apply (case_tac "(T, (newDag D T TM P Q), D)" rule: replaceTip.cases)
  (*D = Tip*)
  apply (simp add: newDag_def)
  apply (case_tac "length TM = 1", simp add: newDagSimp_def)
  apply (subgoal_tac "leftP T \<noteq> P \<and> rightP T \<noteq> Q", simp add: newDagSimpQ_def newDagSimpA_def)
  using segmentCompWithDag apply blast
  apply (simp add: segmentCompWithDag)
  apply (simp add: newDagFirst_def newDagFirstY_def)
  (*D = Node Tl x Tr*)
  apply (simp)
sorry*)

lemma uniqueXAfterReplace[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  T \<in> set (tDagList D) \<Longrightarrow> uniqueXCoord (xDagList (replaceTip T (newDag D T TM P Q) D))"
by (simp)



lemma addSegmentsUnicX: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow> uniqueXCoord (xDagList (addSegmentToTrapezoidalMap D P Q))"
  apply (simp add: addSegmentToTrapezoidalMap_def)
  apply (subgoal_tac "\<forall> T. T \<in> set (intersectedTrapez D P Q) \<longrightarrow> T \<in> set (tDagList D)")
  apply (auto)
  
oops

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




lemma "pointInDag D Q \<Longrightarrow> pointInDag D P \<Longrightarrow> leftFrom P Q \<Longrightarrow> vertexInTramMap D \<Longrightarrow>
  vertexInTramMap (replaceTip T (newDag D T [T] P Q) D)"
  apply (induct T "newDag D T [T] P Q" D rule: replaceTip.induct)
  apply (simp add: vertexInTramMap_def, safe, simp)
  apply (simp add: newDag_def newDagSimp_def)
  apply (case_tac "leftP oT \<noteq> P \<and> rightP oT \<noteq> Q", simp add: newDagSimpQ_def newDagSimpA_def)
    using leftFrom_def pointInTrapez_def apply auto[1]
oops
    
lemma "pointInDag D Q \<Longrightarrow> pointInDag D P \<Longrightarrow> leftFrom P Q \<Longrightarrow> vertexInTramMap D \<Longrightarrow> isTramMap D \<Longrightarrow>
  vertexInTramMap(addSegmentToTrapezoidalMap D P Q)"
  apply (simp add: addSegmentToTrapezoidalMap_def)
  apply (simp add: intersectedTrapez_def del: followSegment.simps)
  apply (case_tac "xCoord (rightP ((queryTrapezoidMap D P))) \<ge> xCoord Q")
    apply (simp)
    apply (simp add: newDag_def newDagSimp_def newDagSimpQ_def newDagSimpA_def)
oops

end