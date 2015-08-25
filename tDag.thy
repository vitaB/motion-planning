(*Datentyp trapez und directed acyclic graph(tDag)-struktur für Trapeze*)

theory tDag
imports polygon
begin

(*Definition für Trapez ((a,b),(c,d),e,f)) top: (a,b), bottom:(c,d), leftP:e, rightP: f
  a=fst(fst p), b = snd(fst p), c=fst(fst(snd p)), d=snd(fst(snd p)), e=fst(snd(snd p)), f=snd(snd(snd p))*)
typedef trapez = "{p::((point2d*point2d)*(point2d*point2d)*point2d*point2d). True}" by (auto)
lemma [simp]: "fst (Rep_trapez (Abs_trapez (a, c, e, f))) = a" by (metis Abs_trapez_inverse Collect_const UNIV_I fst_conv) 
lemma [simp]:"fst(snd (Rep_trapez (Abs_trapez (a, c, e, f)))) = c" by (metis Abs_trapez_inverse Collect_const UNIV_I fst_conv snd_conv)
lemma [simp]:"fst(snd(snd (Rep_trapez (Abs_trapez (a, c, e, f))))) = e" by (metis Abs_trapez_inverse Collect_const UNIV_I fst_conv snd_conv) 
lemma [simp]:"snd(snd(snd (Rep_trapez (Abs_trapez (a, c, e, f))))) = f" by (metis Abs_trapez_inverse Collect_const UNIV_I snd_conv) 

(*identifiers for Trapez-parts*)
definition topT :: "trapez \<Rightarrow> (point2d\<times>point2d)" where  "topT T \<equiv> fst(Rep_trapez T)"
definition bottomT :: "trapez \<Rightarrow> (point2d\<times>point2d)" where "bottomT T \<equiv> fst(snd(Rep_trapez T))"
definition leftP :: "trapez \<Rightarrow> point2d" where "leftP T \<equiv> fst(snd(snd(Rep_trapez T)))"
definition rightP :: "trapez \<Rightarrow> point2d" where "rightP T \<equiv> snd(snd(snd(Rep_trapez T)))"
(*Lemmas zum reduzieren von trapez Termen*)
lemma topT [simp]: "topT (Abs_trapez (a, b, e, f)) = a" by (auto simp add: topT_def Abs_trapez_inverse)
lemma bottomT [simp]: "bottomT (Abs_trapez (a , b, e, f)) = b" by (auto simp add: bottomT_def Abs_trapez_inverse)
lemma leftP [simp]: "leftP (Abs_trapez (a, b, e, f)) = e" by (auto simp add: leftP_def Abs_trapez_inverse)
lemma rightP [simp]: "rightP (Abs_trapez (a, b, e, f)) = f" by (auto simp add: rightP_def Abs_trapez_inverse)

definition "isTrapez p \<equiv> 
  leftFromPoint (leftP p) (rightP p) (*e links von f*)
  \<and> leftFromPoint (fst(topT p)) (snd(topT p)) (*a ist links von b*)
  \<and> leftFromPoint (fst(bottomT p)) (snd(bottomT p)) (*c ist links von d*) 
  \<and> xCoord (leftP p) \<ge> xCoord (fst(topT p)) \<and> xCoord (leftP p) \<ge> xCoord (fst(bottomT p)) (*e \<ge> a \<and> c*)
  \<and> xCoord (rightP p) \<le> xCoord (snd(topT p)) \<and> xCoord (rightP p) \<le> xCoord (snd(bottomT p))(*f \<le> b \<and> d*)
  (*e ist zwischen ab und cd oder e=a oder e=c*)
  \<and> (signedArea (fst(topT p)) (snd(topT p)) (leftP p) \<le> 0 \<and> signedArea (fst(bottomT p)) (snd(bottomT p)) (leftP p) \<ge> 0) (*e ist zwischen ab und cd*)
  \<and> (signedArea (fst(topT p)) (snd(topT p)) (rightP p) \<le> 0 \<and> signedArea (fst(bottomT p)) (snd(bottomT p)) (rightP p) \<ge> 0) (*f ist zwischen ab und cd*)
  \<and> ( (*echtes Trapez oder Dreieck*)
    (leftTurn (fst(bottomT p)) (snd(bottomT p)) (fst(topT p)) \<and> leftTurn (fst(bottomT p)) (snd(bottomT p)) (snd(topT p)) ) (*a und b über c d*)
    \<or> (leftTurn (fst(bottomT p)) (snd(bottomT p)) (fst(topT p)) \<and> fst(bottomT p) = snd(bottomT p) \<and> snd(bottomT p) = rightP p )  (*oder a ist über cd und d=b=f*)
    \<or> (fst(topT p) = fst(bottomT p) \<and> fst(bottomT p) = leftP p \<and> leftTurn (fst(bottomT p)) (snd(bottomT p)) (snd(topT p)) ) (*oder a=c=e und b über c d*)
    )" 
definition "isTrapezList TL \<equiv> \<forall> i < length TL. isTrapez (TL!i)"

(*jeder Punkt der auf der xCoordinate von rightP steht und von topT und bottomT eingegrenzt wird*)
definition pointOnLeftT :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where
  "isTrapez T \<Longrightarrow> pointOnLeftT T p \<equiv> rightTurn (fst(topT T)) (snd(topT T)) p
    \<and> leftTurn (fst(bottomT T)) (snd(bottomT T)) p \<and> xCoord (leftP T) = xCoord p"
definition pointOnRightT :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where
  "isTrapez T \<Longrightarrow> pointOnRightT T p \<equiv> rightTurn (fst(topT T)) (snd(topT T)) p
    \<and> leftTurn (fst(bottomT T)) (snd(bottomT T)) p \<and> xCoord (rightP T) = xCoord p"
  

lemma leftPRigthFromRightP [simp] : "isTrapez T \<Longrightarrow> leftFromPoint (leftP T) (rightP T)"
  by (simp add: isTrapez_def)


(*topT und bottomT sind segmente*)
lemma topTSegment [simp]: "isTrapez T \<Longrightarrow> segment (fst(topT T)) (snd(topT T))"
  apply (cases T, subgoal_tac "xCoord (fst(topT T)) \<noteq> xCoord (snd(topT T))")
  apply (simp add: isTrapez_def)
by (metis (no_types, lifting) isTrapez_def dual_order.irrefl leftFromPoint_def)
lemma bottomTSegment [simp]: "isTrapez T \<Longrightarrow>segment (fst(bottomT T)) (snd(bottomT T))"
  apply (cases T, subgoal_tac "xCoord (fst(bottomT T)) \<noteq> xCoord (snd(bottomT T))")
  apply (simp add: isTrapez_def)
by (metis (no_types, lifting) isTrapez_def leftFromPoint_def less_irrefl)

(*Beweise über die Positionen der Ecken vom Trapez*)
(*mind. einer der Ecken von topT ist über bottomT*)
lemma topAboveBottom [intro] :"isTrapez T \<Longrightarrow> leftTurn (fst (bottomT T)) (snd (bottomT T)) (fst (topT T))
  \<or> leftTurn (fst (bottomT T)) (snd (bottomT T)) (snd (topT T))"
  by (auto simp add: isTrapez_def)
(*leftP ist über bottom T oder ist die linke Ecke von bottomT.
das muss in die definition von Trapez rein! allerdings erweitern, da beim Dreicek auch die Entgegengesetzte Ecke beachtet werden muss
* bläht die Definiton von trapez unnötig auf (?)*)
lemma leftPPos [intro] : "isTrapez T \<Longrightarrow> leftTurn (fst(bottomT T)) (snd(bottomT T)) (leftP T) \<or> (fst(bottomT T) = leftP T)"
  apply (simp add: leftP_def bottomT_def del: leftRightTurn leftTurnRotate leftTurnRotate2,
    cases T, simp del: leftRightTurn leftTurnRotate leftTurnRotate2)
oops
lemma rightPPos [intro] : "isTrapez T \<Longrightarrow> rightTurn (fst(topT T)) (snd(topT T)) (rightP T) \<or> (snd(topT T) = rightP T)"
oops


(*Trapez Equiv.*)
lemma trapezSameCoord [simp]: "(Abs_trapez ((a,b),(c,d),e,f) = Abs_trapez ((a',b'),(c',d'),e',f'))
  \<longleftrightarrow> (a=a'\<and> b=b' \<and> c=c' \<and> d=d' \<and> e=e' \<and> f=f')"
  by (metis bottomT leftP rightP topT)
definition trapezNotEq :: "trapez \<Rightarrow> trapez \<Rightarrow> bool" where
  "trapezNotEq A B \<equiv> A \<noteq> B"

(*Trapez A ist benachbart mit Trapez B*)
definition trapezNeighbor :: "trapez \<Rightarrow> trapez \<Rightarrow> bool" where
  "trapezNeighbor A B \<equiv> (rightP B = leftP A \<or> rightP A = leftP B)
    \<and> ((topT A = topT B) \<or> (bottomT A = bottomT B))"
lemma trapezNeighborSym: "trapezNeighbor A B \<longleftrightarrow> trapezNeighbor B A"
  by(auto simp add: trapezNeighbor_def)

(*Linke Ecken sind rechts von den rechten Ecken*)
lemma trapezNeighbour1 : "isTrapez T \<Longrightarrow> isTrapez Ts \<Longrightarrow> rightP T = leftP Ts \<Longrightarrow>
  leftFromPoint (rightP T) (rightP Ts)"
  by (cases T, simp)
lemma trapezNeighbour2 : "isTrapez T \<Longrightarrow> isTrapez Ts \<Longrightarrow> rightP T = leftP Ts \<Longrightarrow>
  leftFromPoint (leftP T) (leftP Ts)"
  by (metis leftPRigthFromRightP)


(*ein Punkt P ist im Trapez T, wenn es auf den Kanten liegt, oder innerhalb des T*)
definition pointInTrapez :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where 
  "pointInTrapez T P \<equiv> xCoord P \<le> xCoord (rightP T) \<and> xCoord P \<ge> xCoord (leftP T)
  \<and> signedArea (fst(bottomT T)) (snd(bottomT T)) P \<ge> 0 \<and> signedArea (fst(topT T)) (snd(topT T)) P \<le> 0"
definition pointInTrapezS :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where 
  "pointInTrapezS T P \<equiv> xCoord P \<le> xCoord (rightP T) \<and> xCoord P \<ge> xCoord (leftP T)
  \<and> leftTurn (fst(bottomT T)) (snd(bottomT T)) P  \<and> rightTurn (fst(topT T)) (snd(topT T)) P
  \<and> P \<noteq> rightP T \<and> P \<noteq> leftP T"


(*definition trapezSegmentCrossing :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "trapezSegmentCrossing T P Q \<equiv> crossing (fst (topT T)) (snd (topT T)) P Q
    \<or> crossing (fst (bottomT T)) (snd (bottomT T)) P Q"*)

(******directed acyclic graph*)
(*Knoten des graphen kann enweder ein Endpunkt sein, oder ein Segment*)
datatype kNode = xNode "point2d" | yNode "(point2d\<times>point2d)"

(*x-nodes stores a segment endpoint that defines a vertical extension in the trapezoid map,
and has leftChild and rightChild pointers to nodes.*)
(*y-node stores a line segment and its children are also recorded by the pointers are aboveChild
and belowChild depending on whether the child item is above or below the segment stored at the y-node.*)
datatype tDag = Tip "trapez" | Node "tDag" kNode "tDag"

(*Wandle DAG in eine Trapez-Liste um*)
primrec tDagList :: "tDag \<Rightarrow> trapez list" where
  "tDagList (Tip a) = [a]"
  | "tDagList (Node Tl x Tr) = ((tDagList Tl)@(tDagList Tr))"

(*wann ist ein Trapez im Baum*)
primrec tipInDag :: "trapez \<Rightarrow> tDag \<Rightarrow> bool" where
  "tipInDag T (Tip D) = (if (T = D) then True else False)"
  | "tipInDag T (Node Tl x Tr) = (tipInDag T Tl \<or> tipInDag T Tr)"

lemma tDagListComplete : "tipInDag T D \<longleftrightarrow> T \<in> set (tDagList D)" by (induction D, auto)
lemma tDagListNotEmpty[dest] : "tDagList D = [] \<Longrightarrow> False" by (induction D, auto)

(*wann ist ein Punkt im tDag*)
definition pointInDag :: "tDag \<Rightarrow> point2d \<Rightarrow> bool" where
  "pointInDag D A \<equiv> \<exists> i < length (tDagList D). pointInTrapez ((tDagList D)!i) A"

(*Input Tip welches entfernt wird, tDag welches hinzugefügt wird, tDag-tree in dem ersetzt werden soll
Output: neues tDag-tree*)
(* wie verbiete ich replaceTip a D D?*)
fun replaceTip :: "trapez \<Rightarrow> tDag \<Rightarrow> tDag \<Rightarrow> tDag" where
  "replaceTip oT nT (Tip D) = (if (D = oT) then (nT) else (Tip D))"
 |"replaceTip oT nT (Node Tl x Tr) = Node (replaceTip oT nT Tl) x (replaceTip oT nT Tr)"
(*keine unendliche regression*)
lemma "a\<noteq>b \<Longrightarrow> replaceTip a (Node (Tip a) (xNode (c)) (Tip b)) (Node (Tip a) (xNode (c)) (Tip b))
  = (Node ((Node (Tip a) (xNode (c)) (Tip b))) (xNode (c)) (Tip b))" by (auto)

lemma replaceMiss [simp]: "\<not>tipInDag oT D \<Longrightarrow> replaceTip oT nT D = D"
  by (induction oT nT D rule: replaceTip.induct, case_tac "oT = D", simp+)
lemma replaceAfter: "\<not>tipInDag oT nT \<Longrightarrow> \<not>tipInDag oT (replaceTip oT nT D)"
  by (induction oT nT D rule: replaceTip.induct, simp+)
lemma replaceAfter1 : "tipInDag oT nT \<Longrightarrow> tipInDag oT D \<Longrightarrow> tipInDag oT (replaceTip oT nT D)"
  by (induction oT nT D rule: replaceTip.induct,case_tac "oT = D", auto)
lemma replaceInDWithD [simp] : "tipInDag a D \<Longrightarrow> tipInDag a (replaceTip a D D)"
  by (auto simp add: replaceAfter1)

(*lemma replaceTrans : "\<not>tipInDag c b \<Longrightarrow> replaceTip c b (replaceTip a b D) = replaceTip a b (replaceTip c b D)"
  apply (induction c b D rule: replaceTip.induct, auto)*)

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


(*ordnungsrelation nach xCoord des linken Eckpunkts eines Trapezes*)
definition trapezOrd :: "trapez \<Rightarrow> real" where
  "trapezOrd T = xCoord (leftP T)"
(*sortierte ausgabe von Trapezen (nach xCoord von leftP geordnet)*)
definition sortedTrapez :: "trapez list \<Rightarrow> trapez list" where
  "sortedTrapez TM \<equiv> sort_key (trapezOrd) TM"
lemma sortedTrapezSimp [simp]: "sortedTrapez [T] = [T]" by (auto simp add: sortedTrapez_def)
(*(*ist P links vom rechten Eckpunkt des Trapez*)
definition trapezOrdL :: " point2d \<Rightarrow> trapez \<Rightarrow> bool" where
  "trapezOrdL P T \<equiv> leftFromPoint P (rightP T)"
(*ist Q links vom linkem Eckpunkt des Trapez*)
definition trapezOrdR :: " point2d \<Rightarrow> trapez \<Rightarrow> bool" where
  "trapezOrdR Q T \<equiv> leftFromPoint (leftP T) Q"

(*sortierte ausgabe von Trapezen (nach xCoord von leftP geordnet)
  und benschnitten so das nur die Trapeze zwischen P und Q ausgegeben werden*)
definition sortedIntersectTrapez :: "trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "sortedIntersectTrapez TM P Q \<equiv> takeWhile (trapezOrdR Q) (dropWhile (trapezOrdL P) (sort_key (trapezOrd) TM))"*)



(*********rBox. 4 Eckige Box um pointListe herum. First Trapez*)
(*Definition wann ist R eine rechteckige Box um PL herum*)
definition pointInRBox :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where 
  "isTrapez R \<Longrightarrow> pointInRBox R P \<equiv> leftFromPoint P (rightP R) \<and> (leftFromPoint (leftP R) P)
  \<and> leftTurn (fst(bottomT R)) (snd(bottomT R)) P \<and> (rightTurn (fst(topT R)) (snd(topT R)) P)"
definition rBoxTrapezS :: "point2d list \<Rightarrow> trapez \<Rightarrow> bool" where
  "rBoxTrapezS PL R \<equiv> (\<forall> i < length PL. pointInRBox R (PL!i)) \<and> isTrapez R"
lemma rBoxTrapezSSimp [simp] : "isTrapez R \<Longrightarrow> rBoxTrapezS [a] R = pointInRBox R a"
  by (auto simp add: rBoxTrapezS_def)
lemma rBoxTrapezSConcat: "rBoxTrapezS (concat PL) R \<Longrightarrow> i < length PL \<Longrightarrow> rBoxTrapezS (PL!i) R"
  apply (subgoal_tac "\<forall> a \<in> set (concat PL). pointInRBox R a")
  apply (auto simp add: rBoxTrapezS_def)
  apply (erule_tac x=i in allE, safe)
  apply (meson nth_mem)+
sorry

(*order for tDag*)
(*jedes Trapez dessen rightP \<le> x ist ist im Tl von Tl x Tr*)
fun tDagOrdX1 :: "tDag \<Rightarrow> real \<Rightarrow> bool" where
  "tDagOrdX1 (Tip T) x = (xCoord(leftP T) < x)"
  | "tDagOrdX1 (Node lf (xNode n) rt) x = (tDagOrdX1 lf x \<and> xCoord n < x)"
  | "tDagOrdX1 (Node lf (yNode n) rt) x = (tDagOrdX1 lf x \<and> tDagOrdX1 rt x)"
fun tDagOrdX2 :: "tDag \<Rightarrow> real \<Rightarrow> bool" where
  "tDagOrdX2 (Tip T) x = (xCoord(rightP T) \<ge> x)"
  | "tDagOrdX2 (Node lf (xNode n) rt) x = (tDagOrdX2 lf x \<and> x > xCoord n)"
  | "tDagOrdX2 (Node lf (yNode n) rt) x = (tDagOrdX2 lf x \<and> tDagOrdX2 rt x)"
fun tDagOrdX :: "tDag \<Rightarrow> bool" where
  "tDagOrdX (Tip T) = True"
  | "tDagOrdX (Node lf (xNode n) rt) = (tDagOrdX1 lf (xCoord n) \<and> tDagOrdX2 rt (xCoord n)
    \<and> tDagOrdX lf \<and> tDagOrdX rt)"
  | "tDagOrdX (Node lf (yNode n) rt) = (tDagOrdX lf \<and> tDagOrdX rt)"
fun tDagOrdY1 :: "tDag \<Rightarrow> (point2d*point2d) \<Rightarrow> bool" where
  "tDagOrdY1 (Tip T) y = (signedArea (fst y) (snd y) (rightP T) \<ge> 0 \<and> signedArea (fst y) (snd y) (leftP T) \<ge> 0)"
  | "tDagOrdY1 (Node lf (yNode n) rt) y = (tDagOrdY1 lf y \<and> tDagOrdY1 rt y
    \<and> signedArea (fst y) (snd y) (fst y) > 0 \<and> signedArea (fst y) (snd y) (snd y) > 0)"
  | "tDagOrdY1 (Node lf (xNode n) rt) y = (tDagOrdY1 lf y \<and> tDagOrdY1 rt y)"
fun tDagOrdY2 :: "tDag \<Rightarrow> (point2d*point2d) \<Rightarrow> bool" where
  "tDagOrdY2 (Tip T) y = (signedArea (fst y) (snd y) (rightP T) \<le> 0 \<and> signedArea (fst y) (snd y) (leftP T) \<le> 0)"
  | "tDagOrdY2 (Node lf (yNode n) rt) y = (tDagOrdY2 lf y \<and> tDagOrdY2 rt y
    \<and> signedArea (fst y) (snd y) (fst y) < 0 \<and> signedArea (fst y) (snd y) (snd y) < 0)"
  | "tDagOrdY2 (Node lf (xNode n) rt) y = (tDagOrdY2 lf y \<and> tDagOrdY2 rt y)"
fun tDagOrdY :: "tDag \<Rightarrow> bool" where
  "tDagOrdY (Tip T) = True"
  | "tDagOrdY (Node lf (xNode n) rt) = (tDagOrdY lf \<and> tDagOrdY rt)"
  | "tDagOrdY (Node lf (yNode n) rt) = (tDagOrdY1 lf n \<and> tDagOrdY2 rt n
    \<and> tDagOrdY lf \<and> tDagOrdY rt)"
(*jedes Trapez in tDag ist so aufgebaut, dass für alle Trapeze im Baum (Node lf k rt) gilt:
  -rechteEcke von Trapez ist links von k
  -rechteEcke ist über der Kante k*)
fun tDagOrdMap :: "tDag \<Rightarrow> bool" where
  "tDagOrdMap (Tip T)  = True"
  | "tDagOrdMap (Node lf (xNode x) rt) = (tDagOrdX lf \<and> tDagOrdX rt)"
  | "tDagOrdMap (Node lf (yNode y) rt) = (tDagOrdY lf \<and> tDagOrdY rt)"



(*alte Definition*)

(*evtl. überprüfung zu aufwendig*)
(*definition trapezCollinearFree :: "trapez \<Rightarrow> bool" where
  "trapezCollinearFree T \<equiv> \<not>collinearList[fst (leftT T), fst (rightT T), snd(rightT T), snd(leftT T)]"

definition trapezIsCPolygon :: "trapez \<Rightarrow> bool" where
  "trapezIsCPolygon T \<equiv> cPolygon[fst (leftT T), fst (rightT T), snd(rightT T), snd(leftT T)]"*)


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


(*
definition rBoxS :: "point2d list \<Rightarrow> point2d list \<Rightarrow> bool" where
  "pointList PL \<Longrightarrow> rBoxS R PL \<equiv> length R = 4 \<and> cPolygon (cyclePath R) \<and> \<not>collinearList R \<and>
  (\<forall> i < length PL. pointInsideCPolygonCCl (cyclePath R) (PL!i))"
*)
(*
(*wandle rBox in ein Trapez um*)
definition rBoxTrapez :: "point2d list \<Rightarrow> trapez" where
  "pointList PL \<Longrightarrow> rBoxS R PL \<Longrightarrow> rBoxTrapez PL \<equiv> Abs_trapez ((hd PL,PL!1),(PL!3,PL!2),hd PL,PL!2)"


(*4eckige Box um pointListen herum ist selbst eine pointList*)
lemma rBoxPointList: "pointLists PL \<Longrightarrow> pointList(
  [Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1, yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (last (yCoordSort (concat PL))) + 1),
  Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1,yCoord (last (yCoordSort (concat PL))) + 1)])"
sorry

(*wie berechnet man eine rBox. Eine 4eckige Box um pointListen herum*)
definition rBox :: "(point2d list) list \<Rightarrow> point2d list" where
  "pointLists PL \<Longrightarrow> rBox PL \<equiv>
  cyclePath([Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1, yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (last (yCoordSort (concat PL))) + 1),
  Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1,yCoord (last (yCoordSort (concat PL))) + 1)])"

lemma rBoxRight : "pointLists PL \<Longrightarrow> rBoxS (rBox PL) (concat PL)"
  apply (simp add: rBox_def)
sorry

(*ersetzte den Term Polygon im Satz*)
lemma rBoxPoly [simp] : "pointLists PL \<Longrightarrow>
  cyclePath([Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1, yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (last (yCoordSort (concat PL))) + 1),
  Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1,yCoord (last (yCoordSort (concat PL))) + 1)])
  \<equiv> [Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1, yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (last (yCoordSort (concat PL))) + 1),
  Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1,yCoord (last (yCoordSort (concat PL))) + 1),
  Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1, yCoord (hd (yCoordSort (concat PL))) - 1)]"
  apply (cut_tac PL=PL in rBoxPointList, assumption)
  apply (auto simp add: rBox_def cyclePath_def)
done*)

(*(*order for tDag*)
(*jedes Trapez dessen rightP \<le> x ist ist im Tl von Tl x Tr*)
fun tDagOrdX1 :: "tDag \<Rightarrow> real \<Rightarrow> bool" where
  "tDagOrdX1 (Tip T) x = (xCoord(rightP T) \<le> x)"
  | "tDagOrdX1 (Node lf (xNode n) rt) x = (tDagOrdX1 lf x \<and> xCoord n < x)"
  | "tDagOrdX1 (Node lf (yNode n) rt) x = tDagOrdX1 lf x"
fun tDagOrdX2 :: "tDag \<Rightarrow> real \<Rightarrow> bool" where
  "tDagOrdX2 (Tip T) x = (xCoord(leftP T) \<ge> x)"
  | "tDagOrdX2 (Node lf (xNode n) rt) x = (tDagOrdX2 lf x \<and> x > xCoord n)"
  | "tDagOrdX2 (Node lf (yNode n) rt) x = tDagOrdX2 lf x"
fun tDagOrdX :: "tDag \<Rightarrow> bool" where
  "tDagOrdX (Tip T) = True"
  | "tDagOrdX (Node lf (xNode n) rt) = (tDagOrdX1 lf (xCoord n) \<and> tDagOrdX2 rt (xCoord n)
    \<and> tDagOrdX lf \<and> tDagOrdX rt)"
  | "tDagOrdX (Node lf (yNode n) rt) = (tDagOrdX lf \<and> tDagOrdX rt)"
fun tDagOrdY :: "tDag \<Rightarrow> (point2d*point2d) \<Rightarrow> bool" where
  "tDagOrdY (Tip T) y = (signedArea (fst y) (snd y) (rightP T) \<ge> 0)"
  | "tDagOrdY (Node lf (yNode n) rt) y = (tDagOrdY lf y
    \<and> signedArea (fst y) (snd y) (fst y) > 0 \<and> signedArea (fst y) (snd y) (snd y) > 0)"
  | "tDagOrdY (Node lf (xNode n) rt) y = tDagOrdY lf y"
fun tDagOrdY1 :: "tDag \<Rightarrow> (point2d*point2d) \<Rightarrow> bool" where
  "tDagOrdY1 (Tip T) y = (signedArea (fst y) (snd y) (rightP T) \<le> 0)"
  | "tDagOrdY1 (Node lf (yNode n) rt) y = (tDagOrdY1 lf y
    \<and> signedArea (fst y) (snd y) (fst y) < 0 \<and> signedArea (fst y) (snd y) (snd y) < 0)"
  | "tDagOrdY1 (Node lf (xNode n) rt) y = tDagOrdY1 lf y"
(*jedes Trapez in tDag ist so aufgebaut, dass für alle Trapeze im Baum (Node lf k rt) gilt:
  -rechteEcke von Trapez ist links von k
  -rechteEcke ist über der Kante k *)
fun tDagOrdMap :: "tDag \<Rightarrow> bool" where
  "tDagOrdMap (Tip T)  = True"
  | "tDagOrdMap (Node lf (xNode x) rt) = (tDagOrdX lf \<and> tDagOrdX rt)"
  | "tDagOrdMap (Node lf (yNode y) rt) = (tDagOrdY lf y \<and> tDagOrdY1 rt y)"
lemma "tDagOrdMap (Node lf (xNode x) rt) \<Longrightarrow>
  i < length (tDagList lf) \<Longrightarrow> xCoord (rightP ((tDagList lf)!i)) \<le> xCoord x"
  apply (auto)
  apply (induction lf "xCoord x" rule: tDagOrdX.induct, auto)
oops*)
end
