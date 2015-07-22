(*Datentyp trapez und directed acyclic graph(dag)-struktur für Trapeze*)

theory tDag
imports rBox
begin

(*Definition für Trapez ((a,b),(c,d),e,f)) top: (a,b), bottom:(c,d), leftP:e, rightP: f*)
typedef trapez = "{p::((point2d*point2d)*(point2d*point2d)*point2d*point2d). 
  leftFromPoint (fst(snd(snd( p)))) (snd(snd(snd(p))))
  \<and> pointAboveSegment (fst(fst p)) (fst(fst(snd p))) (snd(fst(snd p)))
  \<and> pointAboveSegment (snd(fst p)) (fst(fst(snd p))) (snd(fst(snd p)))
  \<and> segment (fst(fst p)) (snd(fst p))
  \<and> segment (fst(fst(snd p))) (snd(fst(snd p)))}"
sorry

(*identifiers for Trapez-parts*)
definition topT :: "trapez \<Rightarrow> (point2d\<times>point2d)" where  "topT T \<equiv> fst(Rep_trapez T)"
lemma topTSegment [simp]: "segment (fst(topT T)) (snd(topT T))"
  by (cases T, simp add: topT_def, (erule conjE)+, metis (no_types, lifting) Rep_trapez mem_Collect_eq)
definition bottomT :: "trapez \<Rightarrow> (point2d\<times>point2d)" where "bottomT T \<equiv> fst(snd(Rep_trapez T))"
lemma bottomTSegment [simp]: "segment (fst(bottomT T)) (snd(bottomT T))"
  by (cases T, simp add: bottomT_def, (erule conjE)+, metis (no_types, lifting) Rep_trapez mem_Collect_eq)
lemma topAboveBottom [simp] :"pointAboveSegment (fst (topT T)) (fst (bottomT T)) (snd (bottomT T)) \<and> pointAboveSegment (snd (topT T)) (fst (bottomT T)) (snd (bottomT T))"
  by (simp add: topT_def bottomT_def, metis (no_types, lifting) Rep_trapez mem_Collect_eq)
definition leftP :: "trapez \<Rightarrow> point2d" where "leftP T \<equiv> fst(snd(snd(Rep_trapez T)))"
definition rightP :: "trapez \<Rightarrow> point2d" where "rightP T \<equiv> snd(snd(snd(Rep_trapez T)))"
lemma leftPRigthFromRightP [simp] : "leftFromPoint (leftP T) (rightP T)"
  by (simp add: leftP_def rightP_def, metis (no_types, lifting) Rep_trapez mem_Collect_eq)

(*Lemmas zum reduzieren von Termen*)
lemma topT [simp] : " topT (Abs_trapez ((a,b),(c,d),e,f)) = (a,b)" sorry
lemma bottomT [simp] : "bottomT (Abs_trapez ((a,b),(c,d),e,f)) = (c,d) " sorry
lemma leftP [simp] : "leftP (Abs_trapez ((a,b),(c,d),e,f)) = e" sorry
lemma rightP [simp] : "rightP (Abs_trapez ((a,b),(c,d),e,f)) = f" sorry

(*Trapez Equiv.*)
lemma trapezSameCoord [simp]: "(Abs_trapez ((a,b),(c,d),e,f) = Abs_trapez ((a',b'),(c',d'),e',f'))
  \<longleftrightarrow> (a=a'\<and> b=b' \<and> c=c' \<and> d=d' \<and> e=e' \<and> f=f')"
sorry
  (*by (metis Abs_trapez_inverse Collect_const UNIV_I fst_conv snd_conv)*)
definition trapezNotEq :: "trapez \<Rightarrow> trapez \<Rightarrow> bool" where
  "trapezNotEq A B \<equiv> A \<noteq> B"

(*Definition für linke und rechte "Strecke"(muss kein segment sein) des Trapez*)
definition leftT :: "trapez \<Rightarrow> (point2d*point2d)" where 
  "xCoord (fst (topT T)) \<noteq> xCoord (snd (topT T)) \<Longrightarrow> xCoord (fst (bottomT T)) \<noteq> xCoord (snd (bottomT T))\<Longrightarrow>
    leftT T \<equiv> vertSegment (topT T) (bottomT T) (leftP T)"
definition rightT :: "trapez \<Rightarrow> (point2d*point2d)" where 
  "xCoord (fst (topT T)) \<noteq> xCoord (snd (topT T)) \<Longrightarrow> xCoord (fst (bottomT T)) \<noteq> xCoord (snd (bottomT T))\<Longrightarrow> 
    rightT T \<equiv> vertSegment (topT T) (bottomT T) (rightP T)"

(*Linke Ecken sind rechts von den rechten Ecken*)
lemma trapezSimp1 :"xCoord (fst (topT T)) \<noteq> xCoord (snd (topT T)) \<Longrightarrow> xCoord (fst (bottomT T)) \<noteq> xCoord (snd (bottomT T))\<Longrightarrow>
  leftFromPoint (leftP T) (fst (rightT T)) \<and> leftFromPoint (leftP T) (snd (rightT T))"
  by (simp add: leftFromPoint_def rightT_def vertSegment_def segment_def, metis leftFromPoint_def leftPRigthFromRightP)
lemma trapezSimp2 :"xCoord (fst (topT T)) \<noteq> xCoord (snd (topT T)) \<Longrightarrow> xCoord (fst (bottomT T)) \<noteq> xCoord (snd (bottomT T))\<Longrightarrow>
  leftFromPoint (fst(leftT T)) (fst (rightT T)) \<and> leftFromPoint (fst(leftT T)) (snd (rightT T))
  \<and> leftFromPoint (snd(leftT T)) (fst (rightT T)) \<and> leftFromPoint (snd(leftT T)) (snd (rightT T))"
  by (cases T, auto simp add: leftFromPoint_def, (metis leftFromPoint_def leftP leftPRigthFromRightP rightP)+)

(*Point in Trapezoidal*)
definition pointInTrapez :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where 
  "pointInTrapez T P \<equiv> leftFromPoint P (rightP T) \<and> \<not>(leftFromPoint P (leftP T))
  \<and> pointAboveSegment P (fst(bottomT T)) (snd(bottomT T)) \<and> pointBelowSegment P (fst(topT T)) (snd(topT T))"



(*evtl. überprüfung zu aufwendig*)
definition trapezCollinearFree :: "trapez \<Rightarrow> bool" where
  "trapezCollinearFree T \<equiv> \<not>collinearList[fst (leftT T), fst (rightT T), snd(rightT T), snd(leftT T)]"

definition trapezIsCPolygon :: "trapez \<Rightarrow> bool" where
  "trapezIsCPolygon T \<equiv> cPolygon[fst (leftT T), fst (rightT T), snd(rightT T), snd(leftT T)]"


(*wandle rBox in ein Trapez um*)
definition rBoxTrapez :: "point2d list \<Rightarrow> trapez" where 
  "pointList R \<Longrightarrow> length R = 4 \<Longrightarrow> cPolygon (cyclePath R) \<Longrightarrow>
  rBoxTrapez R \<equiv> Abs_trapez ((hd R,R!1),(R!3,R!2),hd R,R!2)"

(*lemma rBoxTrapezCollinearFree[simp]: "pointLists PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow> trapezCollinearFree (rBoxTrapez PL)"
  apply (simp add: trapezCollinearFree_def rBoxTrapez_def)
  apply (simp add: leftT_def rightT_def topT_def bottomT_def)
  apply (subgoal_tac "segment (fst ((fst (Rep_trapez (rBoxTrapez PL))))) (fst (fst (Rep_trapez (rBoxTrapez PL))))")
  apply (subgoal_tac "segment (fst (fst (snd (Rep_trapez (rBoxTrapez PL))))) (fst (fst (snd (Rep_trapez (rBoxTrapez PL)))))")
  apply (simp add: vertSegment_def)
sorry*)


(*Knoten des graphen kann enweder ein Endpunkt sein, oder ein Segment*)
datatype_new kNode = xNode "point2d" | yNode "(point2d\<times>point2d)"

(*directed acyclic graph*)
(*x-nodes stores a segment endpoint that defines a vertical extension in the trapezoid map,
and has leftChild and rightChild pointers to nodes.*)
(*y-node stores a line segment and its children are also recorded by the pointers are aboveChild
and belowChild depending on whether the child item is above or below the segment stored at the y-node.*)
datatype_new dag = Tip "trapez" | Node "dag" kNode "dag"

(*Wandle DAG in eine Trapez-Liste um*)
primrec dagList :: "dag \<Rightarrow> trapez list" where
  "dagList (Tip a) = [a]"
  | "dagList (Node Tl x Tr) = ((dagList Tl)@(dagList Tr))"

(*wann ist ein Trapez im Baum*)
fun tipInDag :: "trapez \<Rightarrow> dag \<Rightarrow> bool" where
  "tipInDag T (Tip D) = (if (T = D) then True else False)"
  | "tipInDag T (Node Tl x Tr) = (tipInDag T Tl \<or> tipInDag T Tr)"
lemma dagListComplete : "tipInDag T D \<longleftrightarrow> T \<in> set (dagList D)" by (induction D, auto)

(*Input Tip welches entfernt wird, dag welches hinzugefügt wird, dag-tree in dem ersetzt werden soll
Output: neues dag-tree*)
fun replaceTip :: "trapez \<Rightarrow> dag \<Rightarrow> dag \<Rightarrow> dag" where
  "replaceTip oT nT (Tip D) = (if (D = oT) then (nT) else (Tip D))"
 |"replaceTip oT nT (Node Tl x Tr) = Node (replaceTip oT nT Tl) x (replaceTip oT nT Tr)"

lemma replaceMiss [simp]: "\<not>tipInDag oT D \<Longrightarrow> replaceTip oT nT D = D"
  by (induction oT nT D rule: replaceTip.induct, case_tac "oT = D", simp+)
lemma replaceAfter: "\<not>tipInDag oT nT \<Longrightarrow> \<not>tipInDag oT (replaceTip oT nT D)"
  by (induction oT nT D rule: replaceTip.induct, simp+)

lemma replaceTipSize1 : "size (replaceTip oT (Tip nT) D) = size D"
  by (induction oT "Tip nT" D rule: replaceTip.induct, simp+)
lemma replaceTipSize : "size (replaceTip oT nT D) \<ge> size D"
  by (induction oT nT D rule: replaceTip.induct, simp+)

lemma replaceTipSame [simp] : "replaceTip oT (Tip oT) D = D"
  by (induction oT "(Tip oT)" D rule: replaceTip.induct, simp+)

lemma "nT\<noteq>D\<Longrightarrow> replaceTip oT nT D = replaceTip oT D nT \<Longrightarrow> False"
  apply (induction D, simp)
  apply (case_tac "x = oT")
oops
theorem replaceTipSimp [simp] :"\<not>tipInDag nT' D \<Longrightarrow> replaceTip nT' nT (replaceTip oT (Tip nT') D) = replaceTip oT nT D"
  apply (induction D, case_tac "nT' = x", simp+)
done
theorem "replaceTip oT nT (replaceTip oT' nT' D) = replaceTip oT' nT' (replaceTip oT nT D) \<Longrightarrow> False"
  apply (induction oT nT D rule: replaceTip.induct)
  apply (simp)
  apply (case_tac "oT'= oT")
  apply (case_tac "D = oT'")
  apply (simp)
oops

definition trapezOrd :: "trapez \<Rightarrow> real" where
  "trapezOrd T = xCoord (leftP T)"

fun sortedIntersectTrapez :: "trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "sortedIntersectTrapez [] _ _ = []"
  | "sortedIntersectTrapez (T#TS) P Q = (if (intersect P Q (fst(leftT T)) (snd(leftT T)))
  then (List.insort_insert_key trapezOrd T (sortedIntersectTrapez TS P Q))
  else(sortedIntersectTrapez TS P Q))"


(*fun rightUpperN :: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez" where
  "rightUpperN (Ts#Tl) T P Q =
  (if (rightP T = leftP Ts \<and> pointBelowSegment (leftP Ts) (fst (topT Ts)) (snd (topT Ts)))
    then (Ts)
  else (rightUpperN Tl T P Q))"

fun rightLowerN :: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez" where
  "rightLowerN (Ts#Tl) T P Q =
  (if (rightP T = leftP Ts \<and> pointAboveSegment (leftP Ts) (fst (topT Ts)) (snd (topT Ts)))
    then (Ts)
  else (rightLowerN Tl T P Q))"*)

end
