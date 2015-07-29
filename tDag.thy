(*Datentyp trapez und directed acyclic graph(tDag)-struktur für Trapeze*)

theory tDag
imports polygon
begin

(*Definition für Trapez ((a,b),(c,d),e,f)) top: (a,b), bottom:(c,d), leftP:e, rightP: f
  a=fst(fst p), b = snd(fst p), c=fst(fst(snd p)), d=snd(fst(snd p)), e=fst(snd(snd p)), f=snd(snd(snd p))*)
typedef trapez = "{p::((point2d*point2d)*(point2d*point2d)*point2d*point2d). 
  leftFromPoint (fst(snd(snd( p)))) (snd(snd(snd(p)))) (*e links von f*)
  \<and> (signedArea (fst(fst p)) (snd(fst p)) (fst(snd(snd p))) \<le> 0 \<and> signedArea (fst(fst(snd p))) (snd(fst(snd p))) (fst(snd(snd p))) \<ge> 0) (*e ist zwischen ab und cd*)
  \<and> (signedArea (fst(fst p)) (snd(fst p)) (snd(snd(snd p))) \<le> 0 \<and> signedArea (fst(fst(snd p))) (snd(fst(snd p))) (snd(snd(snd p))) \<ge> 0) (*f ist zwischen ab und cd*)
  \<and> ( (leftTurn (fst(fst(snd p))) (snd(fst(snd p))) (fst(fst p)) \<and> leftTurn (fst(fst(snd p))) (snd(fst(snd p))) (snd(fst p)) ) (*a und b über c d*)
    \<or> ( leftTurn (fst(fst(snd p))) (snd(fst(snd p))) (fst(fst p)) \<and> ((snd(fst(snd p))) = (snd(fst p))) ) (*a ist über cd und d=b*)
    \<or> ( ((fst(fst(snd p))) = (fst(fst p))) \<and> leftTurn (fst(fst(snd p))) (snd(fst(snd p))) (snd(fst p)) ) ) (*a = c und b über c d*)
  \<and> leftFromPoint (fst(fst p)) (snd(fst p)) (*ab ist ein segment, wobei a links von b ist*)
  \<and> leftFromPoint (fst(fst(snd p))) (snd(fst(snd p)))}"(*cd ist ein segment, wobei c links von d ist*)
  apply (simp add: leftFromPoint_def segment_def)
  apply (rule_tac x="Abs_point2d(1,3)" in exI, rule_tac x="Abs_point2d(2,3)" in exI, simp)
  apply (rule_tac x="Abs_point2d(1,1)" in exI, rule_tac x="Abs_point2d(2,1)" in exI,
    rule_tac x="Abs_point2d(1,2)" in exI, rule_tac x="Abs_point2d(2,2)" in exI)
  apply (auto simp add: signedArea_def rightTurn_def)
done  

(*identifiers for Trapez-parts*)
definition topT :: "trapez \<Rightarrow> (point2d\<times>point2d)" where  "topT T \<equiv> fst(Rep_trapez T)"
definition bottomT :: "trapez \<Rightarrow> (point2d\<times>point2d)" where "bottomT T \<equiv> fst(snd(Rep_trapez T))"
definition leftP :: "trapez \<Rightarrow> point2d" where "leftP T \<equiv> fst(snd(snd(Rep_trapez T)))"
definition rightP :: "trapez \<Rightarrow> point2d" where "rightP T \<equiv> snd(snd(snd(Rep_trapez T)))"
lemma leftPRigthFromRightP [simp] : "leftFromPoint (leftP T) (rightP T)"
  by (simp add: leftP_def rightP_def, metis (no_types, lifting) Rep_trapez mem_Collect_eq)
  
(*topT und bottomT sind segmente*)
lemma topTSegment [simp]: "segment (fst(topT T)) (snd(topT T))"
  apply (cases T, subgoal_tac "xCoord (fst(topT T)) \<noteq> xCoord (snd(topT T))")
  apply (simp add: topT_def segment_def, (erule conjE)+, metis (no_types, lifting), simp)
by (metis (no_types, lifting) Rep_trapez dual_order.irrefl leftFromPoint_def mem_Collect_eq topT_def)
lemma bottomTSegment [simp]: "segment (fst(bottomT T)) (snd(bottomT T))"
  apply (cases T, subgoal_tac "xCoord (fst(bottomT T)) \<noteq> xCoord (snd(bottomT T))")
  apply (simp add: bottomT_def segment_def, (erule conjE)+, metis (no_types, lifting), simp)
by (metis (no_types, lifting) Rep_trapez bottomT_def leftFromPoint_def less_irrefl mem_Collect_eq)

(*Beweise über die Positionen der Ecken vom Trapez*)
(*mind. einer der Ecken von topT ist über bottomT*)
lemma topAboveBottom [simp] :"leftTurn (fst (bottomT T)) (snd (bottomT T)) (fst (topT T))
  \<or> leftTurn (fst (bottomT T)) (snd (bottomT T)) (snd (topT T))"
  by (simp add: topT_def bottomT_def, metis (no_types, lifting) Rep_trapez leftRightTurn mem_Collect_eq)
(*leftP ist über bottom T oder ist die linke Ecke von bottomT*)
lemma leftPPos : "leftTurn (fst(bottomT T)) (snd(bottomT T)) (leftP T) \<or> (fst(bottomT T)) = (leftP T)"
  apply (simp add: leftP_def bottomT_def del: leftRightTurn leftTurnRotate leftTurnRotate2,
    cases T, simp del: leftRightTurn leftTurnRotate leftTurnRotate2, safe)
  apply (subgoal_tac "fst ((a, b), (aa, ba), ab, bb) = (a,b) \<and>  snd ((a, b), (aa, ba), ab, bb) = ((aa, ba), ab, bb)
    \<and> fst(snd ((a, b), (aa, ba), ab, bb)) = (aa, ba) \<and> fst(snd(snd ((a, b), (aa, ba), ab, bb))) = ab
    \<and> snd(snd(snd ((a, b), (aa, ba), ab, bb))) = bb")
  apply (simp del: leftRightTurn leftTurnRotate leftTurnRotate2)
  apply (subgoal_tac "leftTurn (fst (fst (snd (Rep_trapez (Abs_trapez ((a, b), (aa, ba), ab, bb))))))
        (snd (fst (snd (Rep_trapez (Abs_trapez ((a, b), (aa, ba), ab, bb))))))
        (fst (snd (snd (Rep_trapez (Abs_trapez ((a, b), (aa, ba), ab, bb)))))) = leftTurn aa ba ab")
  apply (subgoal_tac "fst (fst (snd (Rep_trapez (Abs_trapez ((a, b), (aa, ba), ab, bb))))) = aa \<and> fst (snd (snd (Rep_trapez (Abs_trapez ((a, b), (aa, ba), ab, bb))))) = ab")
  apply (simp del: leftRightTurn leftTurnRotate leftTurnRotate2)

  apply (subgoal_tac "0 \<noteq> signedArea aa ba ab")
  apply (metis leftTurn_def less_eq_real_def)

oops
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


(*Linke Ecken sind rechts von den rechten Ecken*)
lemma trapezNeighbour1 : "rightP T = leftP Ts \<Longrightarrow> leftFromPoint (rightP T) (rightP Ts)"
  by (cases T, simp)
lemma trapezNeighbour2 : "rightP T = leftP Ts \<Longrightarrow> leftFromPoint (leftP T) (leftP Ts)"
  by (cases T, auto)


(*Point in Trapezoidal, evtl. sollte punkt auf allen Kanten akzeptiert werden*)
definition pointInTrapez :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where 
  "pointInTrapez T P \<equiv> leftFromPoint P (rightP T) \<and> \<not>(leftFromPoint P (leftP T))
  \<and> leftTurn (fst(bottomT T)) (snd(bottomT T)) P \<and> \<not>(leftTurn (fst(topT T)) (snd(topT T)) P)"


(*definition trapezPointList :: *)

(*evtl. überprüfung zu aufwendig*)
(*definition trapezCollinearFree :: "trapez \<Rightarrow> bool" where
  "trapezCollinearFree T \<equiv> \<not>collinearList[fst (leftT T), fst (rightT T), snd(rightT T), snd(leftT T)]"

definition trapezIsCPolygon :: "trapez \<Rightarrow> bool" where
  "trapezIsCPolygon T \<equiv> cPolygon[fst (leftT T), fst (rightT T), snd(rightT T), snd(leftT T)]"*)



(*Knoten des graphen kann enweder ein Endpunkt sein, oder ein Segment*)
datatype_new kNode = xNode "point2d" | yNode "(point2d\<times>point2d)"

(*directed acyclic graph*)
(*x-nodes stores a segment endpoint that defines a vertical extension in the trapezoid map,
and has leftChild and rightChild pointers to nodes.*)
(*y-node stores a line segment and its children are also recorded by the pointers are aboveChild
and belowChild depending on whether the child item is above or below the segment stored at the y-node.*)
datatype_new tDag = Tip "trapez" | Node "tDag" kNode "tDag"

(*Wandle DAG in eine Trapez-Liste um*)
primrec tDagList :: "tDag \<Rightarrow> trapez list" where
  "tDagList (Tip a) = [a]"
  | "tDagList (Node Tl x Tr) = ((tDagList Tl)@(tDagList Tr))"

(*wann ist ein Trapez im Baum*)
fun tipInDag :: "trapez \<Rightarrow> tDag \<Rightarrow> bool" where
  "tipInDag T (Tip D) = (if (T = D) then True else False)"
  | "tipInDag T (Node Tl x Tr) = (tipInDag T Tl \<or> tipInDag T Tr)"
lemma tDagListComplete : "tipInDag T D \<longleftrightarrow> T \<in> set (tDagList D)" by (induction D, auto)

(*Input Tip welches entfernt wird, tDag welches hinzugefügt wird, tDag-tree in dem ersetzt werden soll
Output: neues tDag-tree*)
fun replaceTip :: "trapez \<Rightarrow> tDag \<Rightarrow> tDag \<Rightarrow> tDag" where
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


(*zwei Trapeze sind benachbart entland der Strecke PQ, die linke Ecke eines Trapezes gleich der rechten Ecke des anderen Trapezes
und wenn topT gleich sind, falls PQ über rightPT bzw. bottomT gleich sind, falls PQ unter rightP.*)
definition neighbTrapez:: "tDag \<Rightarrow> trapez \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "neighbTrapez D T Ts P Q \<equiv> rightP T = leftP Ts \<and>
  ((rightTurn P Q (rightP T) \<and> topT T = topT Ts) \<or> (leftTurn P Q (rightP T) \<and> bottomT T = bottomT Ts))"
(*gib den nächsten Nachbarn von einem Trapez folgend der Strecke PQ  aus der Trapez-Liste
Input: tDag, tDagList geordnet nach der x-Coordinate von leftP, Strecke PQ
Output: nächster trapez-Nachbar, wenn man PQ folgt*)
(*es muss ein Nachbar geben!*)
fun nextTrapez :: "tDag \<Rightarrow> trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez" where
  "nextTrapez D (Ts#Tm) T P Q = (if(neighbTrapez D T Ts P Q) then(Ts) else(nextTrapez D Tm T P Q))"


(*ordnungsrelation nach xCoord des linken Eckpunkts eines Trapezes*)
definition trapezOrd :: "trapez \<Rightarrow> real" where
  "trapezOrd T = xCoord (leftP T)"
(*ist P links vom rechten Eckpunkt des Trapez*)
definition trapezOrdL :: " point2d \<Rightarrow> trapez \<Rightarrow> bool" where
  "trapezOrdL P T \<equiv> leftFromPoint P (rightP T)"
(*ist Q links vom linkem Eckpunkt des Trapez*)
definition trapezOrdR :: " point2d \<Rightarrow> trapez \<Rightarrow> bool" where
  "trapezOrdR Q T \<equiv> leftFromPoint (leftP T) Q"

(*sortierte ausgabe von Trapezen (nach xCoord von leftP geordnet)
  und benschnitten so das nur die Trapeze zwischen P und Q ausgegeben werden*)
definition sortedIntersectTrapez :: "trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "sortedIntersectTrapez TM P Q \<equiv> takeWhile (trapezOrdR Q) (dropWhile (trapezOrdL P) (sort_key (trapezOrd) TM))"



(*rBox. First Trapez*)

(*Definition wann ist R eine rechteckige Box um PL herum*)
definition rBoxS :: "point2d list \<Rightarrow> point2d list \<Rightarrow> bool" where
  "pointList PL \<Longrightarrow> rBoxS R PL \<equiv> length R = 4 \<and> cPolygon (cyclePath R) \<and> \<not>collinearList R \<and>
  (\<forall> i < length PL. pointInsideCPolygonCCl (cyclePath R) (PL!i))"

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
done




(*alte Definition*)

(*(*Definition für linke und rechte "Strecke"(muss kein segment sein) des Trapez*)
definition leftT :: "trapez \<Rightarrow> (point2d*point2d)" where 
  "xCoord (fst (topT T)) \<noteq> xCoord (snd (topT T)) \<Longrightarrow> xCoord (fst (bottomT T)) \<noteq> xCoord (snd (bottomT T))\<Longrightarrow>
    leftT T \<equiv> vertSegment (topT T) (bottomT T) (leftP T)"
(*wenn leftP, der linke Eckpunkt von topT und bottomT, dann ist leftT kein segment*)
lemma "xCoord (fst (topT T)) \<noteq> xCoord (snd (topT T)) \<Longrightarrow> xCoord (fst (bottomT T)) \<noteq> xCoord (snd (bottomT T)) \<Longrightarrow>
   leftP T = fst(topT T) \<and> leftP T = fst(bottomT T) \<Longrightarrow> fst (leftT T) = snd (leftT T)"
  apply (simp add: leftT_def vertSegment_def lineFunktionY_def)
  apply (cases T, simp, safe)
  apply ((simp add: leftFromPoint_def not_less_iff_gr_or_eq, 
    metis leftFromPoint_def leftP leftPRigthFromRightP not_less_iff_gr_or_eq rightP)+)
done
(*Falsch*)
lemma "xCoord (fst (topT T)) \<noteq> xCoord (snd (topT T)) \<Longrightarrow> xCoord (fst (bottomT T)) \<noteq> xCoord (snd (bottomT T)) \<Longrightarrow>
   leftP T = fst(topT T) \<or> leftP T = fst(bottomT T) \<Longrightarrow> fst (leftT T) = snd (leftT T)"
  apply (simp add: leftT_def vertSegment_def lineFunktionY_def)
  apply (cases T, simp, safe)
  apply ((simp add: leftFromPoint_def not_less_iff_gr_or_eq, 
    metis leftFromPoint_def leftP leftPRigthFromRightP not_less_iff_gr_or_eq rightP)+)
done
lemma "xCoord (fst (topT T)) \<noteq> xCoord (snd (topT T)) \<Longrightarrow> xCoord (fst (bottomT T)) \<noteq> xCoord (snd (bottomT T)) \<Longrightarrow>
  \<not>collinear (leftP T) (fst((topT T))) (snd((topT T))) \<or> \<not>collinear (leftP T) (fst((bottomT T))) (snd((bottomT T))) \<Longrightarrow>
  segment (fst (leftT T)) (snd (leftT T))"
oops
definition rightT :: "trapez \<Rightarrow> (point2d*point2d)" where 
  "xCoord (fst (topT T)) \<noteq> xCoord (snd (topT T)) \<Longrightarrow> xCoord (fst (bottomT T)) \<noteq> xCoord (snd (bottomT T))\<Longrightarrow> 
    rightT T \<equiv> vertSegment (topT T) (bottomT T) (rightP T)"

lemma trapezSimp1 :"xCoord (fst (topT T)) \<noteq> xCoord (snd (topT T)) \<Longrightarrow> xCoord (fst (bottomT T)) \<noteq> xCoord (snd (bottomT T))\<Longrightarrow>
  leftFromPoint (leftP T) (fst (rightT T)) \<and> leftFromPoint (leftP T) (snd (rightT T))"
  by (simp add: leftFromPoint_def rightT_def vertSegment_def segment_def, metis leftFromPoint_def leftPRigthFromRightP)
lemma trapezSimp2 :"xCoord (fst (topT T)) \<noteq> xCoord (snd (topT T)) \<Longrightarrow> xCoord (fst (bottomT T)) \<noteq> xCoord (snd (bottomT T))\<Longrightarrow>
  leftFromPoint (fst(leftT T)) (fst (rightT T)) \<and> leftFromPoint (fst(leftT T)) (snd (rightT T))
  \<and> leftFromPoint (snd(leftT T)) (fst (rightT T)) \<and> leftFromPoint (snd(leftT T)) (snd (rightT T))"
  by (cases T, auto simp add: leftFromPoint_def, (metis leftFromPoint_def leftP leftPRigthFromRightP rightP)+)*)


(*ein Trapez wird von PQ geschnitten, wenn es auf zwischen leftT und PQ ein crossing gibt.*)
(*definition trapezCrossing :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "trapezCrossing T P Q =
  (if (crossing P Q (fst(leftT T)) (snd(leftT T)))(*hier lässt sich evtl. mit einer anderen herangesweise des intersect, die beweisführung verbessern*)
  then (True) else (False))"*)

(*Trapeze das von PQ geschnitten wird, sortiert nach der xCoord der linken Ecke*)
(*fun sortedIntersectTrapez :: "trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "sortedIntersectTrapez [] _ _ = []"
  | "sortedIntersectTrapez (T#TS) P Q = (if (trapezCrossing T P Q)
  then (List.insort_insert_key trapezOrd T (sortedIntersectTrapez TS  P Q))
  else(sortedIntersectTrapez TS P Q))"*)


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
