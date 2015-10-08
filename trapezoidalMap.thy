theory trapezoidalMap
imports tDag (*"~~/src/HOL/Library/Multiset"*)
begin


(*gehe solange bis zum nächsten Nachbarn bis gesuchte Ecke gefunden ist
Input: funktion die linke/rechte Ecke vom Trapez gibt, Liste mit Trapezen durch die PQ geht,
  Entscheidung Trapez-Ecke über/unter segment PQ liegt, Strecke PQ
Output: nächste linke/rechte Ecke die über/unter dem Segment P/Q liegt*)
fun nextCorner :: "(trapez \<Rightarrow> point2d) \<Rightarrow> trapez list \<Rightarrow> (point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool)
  \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
    "nextCorner f [TM] _  _ _ = f TM"
    |" nextCorner f (TM#TS) g P Q = (if (g (f TM) P Q) then (f TM) else (nextCorner f TS g P Q))"

(*gehe solange von T zum nächsten linken Nachbarn, bis leftP des Trapez über PQ liegt*)
definition topLeftCorner:: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "topLeftCorner TM T P Q \<equiv> nextCorner leftP (dropWhile (trapezNotEq T) (rev TM)) leftTurn P Q"
(*gehe solange von T zum nächsten rechten Nachbarn, bis rightP des Trapez über PQ liegt*)
definition topRightCorner :: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "topRightCorner TM T P Q \<equiv> nextCorner rightP (dropWhile (trapezNotEq T) TM) leftTurn P Q"
(*gehe solange von T zum nächsten linken Nachbarn, bis leftP des Trapez unter PQ liegt*)
definition bottomLeftCorner :: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "bottomLeftCorner TM T P Q \<equiv> nextCorner leftP (dropWhile (trapezNotEq T) (rev TM)) rightTurn P Q"
(*gehe solange von T zum nächsten rechten Nachbarn, bis rightP des Trapez unter PQ liegt*)
definition bottomRightCorner :: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "bottomRightCorner TM T P Q \<equiv> nextCorner rightP (dropWhile (trapezNotEq T) TM) rightTurn P Q"


(*order for tDag*)
(*Algorithm QueryTrapezoidMap(tDag,point2d)
Input: T is the trapezoid map search structure, n is a node in the search structure and p is a query point.
Output:  A pointer to the node in D for the trapezoid containing the point p.*)
fun queryTrapezoidMap :: "tDag \<Rightarrow> point2d \<Rightarrow> trapez" where
  "queryTrapezoidMap (Tip T) _ =  T"
  |"queryTrapezoidMap (Node lf (xNode n) rt) p = 
   (if (xCoord p < xCoord n) then (queryTrapezoidMap lf p) else (queryTrapezoidMap rt p))"
  |"queryTrapezoidMap (Node lf (yNode x) rt) p =
  (*lf ist über dem segment x, rt ist unter dem segment*)
   (if (leftTurn (fst x) (snd x) p) then (queryTrapezoidMap lf p) else (queryTrapezoidMap rt p))"
(*jedes Trapez was mit queryTrapezoidMap gefunden wird, muss auch mit tipInDag gefunden werden können*)
lemma queryTrapezoidMapInDag[simp]: "tipInDag (queryTrapezoidMap D P) D"
  apply (subgoal_tac "(queryTrapezoidMap D P) \<in> set (tDagList D)", simp add: tDagListComplete)
by (induct D P rule: queryTrapezoidMap.induct, auto)
lemma queryTrapezoidMapInDagList[simp]: "(queryTrapezoidMap D Q) \<in> set (tDagList D)"
  using queryTrapezoidMapInDag tDagListComplete by blast
  
lemma queryTrapezoidMapIsTrapez[simp]:"trapezList (tDagList D) \<Longrightarrow> isTrapez (queryTrapezoidMap D P)"
  using queryTrapezoidMapInDag tDagListComplete trapezList_def by blast

(*alle Punkte die in rBox liegen fidet quiryTrapezoidMap*)
lemma pointInRBox1: "\<forall> a. pointInDag (Tip R) a \<longrightarrow> pointInTrapez (queryTrapezoidMap (Tip R) a) a"
  apply (auto, simp add: pointInDag_def)
done
lemma pointInRBox:"rBoxTrapezS PL R \<Longrightarrow> \<forall> a \<in> set PL. pointInTrapez (queryTrapezoidMap (Tip R) a) a"
  apply (auto)
  apply (auto simp add: rBoxTrapezS_def pointInTrapez_def)
  using leftFrom_def pointInRBox_def apply auto[1]
  using leftFrom_def pointInRBox_def apply auto[1]
  using pointInRBox_def rightTurn_def apply fastforce
  using pointInRBox_def rightTurn_def apply fastforce
done

(*alle Punkte in der trapezoidalMap müssen im richtigen Trapez gefunden werden*)
definition pointsInTramMap :: "tDag \<Rightarrow> bool" where
   "pointsInTramMap D \<equiv> \<forall> a. pointInDag D a \<longrightarrow> pointInTrapez (queryTrapezoidMap D a) a"
lemma pointInQueryTrapezoid: "trapezList (tDagList D) \<Longrightarrow> pointsInTramMap D \<Longrightarrow> pointInDag D P \<Longrightarrow>
  xCoord P \<le> xCoord (rightP (queryTrapezoidMap D P))"
  using pointInTrapezSimp pointsInTramMap_def queryTrapezoidMapInDag tDagListComplete
  trapezList_def by blast


(*****create new Dag to replace intersected Trapez*)
(*Einfacher Fall: allgemeinFall*)
definition newDagSimpA :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagSimpA T P Q \<equiv>
   Node (Tip (Abs_trapez (topT T,(P,Q),P,Q)))
    (yNode (P,Q))
   (Tip (Abs_trapez ((P,Q),bottomT T,P,Q)))"
lemma newDagSimpANotSame[simp]: "newDagSimpA T P Q \<noteq> Tip T"
  by (simp add: newDagSimpA_def)

(*Einfacher Fall: füge Q hinzu, P bereits betrachtet*)
definition newDagSimpQ :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagSimpQ T P Q \<equiv>
    Node (newDagSimpA T P Q)
      (xNode Q)
    (Tip (Abs_trapez(topT T,bottomT T,Q,rightP T)))"
lemma newDagSimpQNotSame[simp]: "newDagSimpQ T P Q \<noteq> Tip T"
  by (simp add: newDagSimpQ_def)

(*Einfacher Fall: wenn P und Q in T liegen*)
definition newDagSimp :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagSimp  T P Q \<equiv> (
    if((leftP T \<noteq> P \<and> rightP T \<noteq> Q)) (*P und Q sind keine Endpunkte von Trapezen*)
    then (
      Node (Tip(Abs_trapez(topT T,bottomT T,leftP T,P)))
        (xNode P)
        (newDagSimpQ T P Q)
    ) else( if (leftP T = P \<and> rightP T \<noteq> Q) (*P ist ein Endpunkt, Q nicht*)
        then (newDagSimpQ T P Q)
        else (if(leftP T \<noteq> P \<and> rightP T = Q) (*Q ist ein Endpunkt, P nicht*)
          then (Node (Tip (Abs_trapez(topT T, bottomT T, leftP T, P)))
            (xNode P)
           (newDagSimpA T P Q)
           (*P und Q sind Endpunkte*)
           )else (newDagSimpA T P Q)
      )))"
lemma newDagSimpNotSame[simp]: "newDagSimp T P Q \<noteq> Tip T"
  by (simp add: newDagSimp_def)
lemma newDagSimpTrapez:"\<forall> a \<in> set (tDagList (newDagSimp R p q)). isTrapez (a)"
  apply (auto simp add: newDagSimp_def newDagSimpQ_def newDagSimpA_def)
oops
lemma newDagSimpRBoxTrapez: "leftFrom p q \<Longrightarrow> rightP R \<noteq> q \<Longrightarrow> p \<noteq> leftP R \<Longrightarrow> 
  newDagSimp R p q = Node(Tip (Abs_trapez (topT R,bottomT R, leftP R, p)))(xNode p)
  (Node(Node(Tip (Abs_trapez(topT R,(p,q),p,q)))(yNode (p,q))(Tip (Abs_trapez((p,q),bottomT R, p, q))))
  (xNode q)(Tip (Abs_trapez (topT R,bottomT R, q, rightP R))))"
by (auto simp add: newDagSimp_def newDagSimpQ_def newDagSimpA_def)

(*ersetze mittlere Trapeze, d.h. P liegt in T0, Q liegt in Tn und Trapez Ti(0<i<n) soll ersetzt werden*)
definition newDagM :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
   "newDagM  T TM P Q \<equiv>
   Node (Tip (Abs_trapez(topT T,(P,Q),(topLeftCorner TM T P Q), (topRightCorner TM T P Q))))
      (yNode (P,Q))
    (Tip (Abs_trapez((P,Q), bottomT T, (bottomLeftCorner TM T P Q), (bottomRightCorner TM T P Q))))"
lemma newDagMNotSame[simp]: "newDagM T TM P Q \<noteq> Tip T"
  by (simp add: newDagM_def)

(*gegebenes Trapez wird durch 2 neue Trapeze ersetzt; geteilt durch die Strecke PQ*)
definition newDagFirstY :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagFirstY T TM P Q \<equiv>
  Node (Tip (Abs_trapez(topT T, (P,Q), P, (topRightCorner TM T P Q))))
    (yNode (P,Q))
   (Tip (Abs_trapez((P,Q), bottomT T, P, (bottomRightCorner TM T P Q))))"

(*Das erste Trapez soll ersetzt werden, zu überprüfen ist ob Ecke im Trapez ist oder auf der Kante*)
definition newDagFirst :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagFirst T TM P Q \<equiv> (
  if (leftP T = P) then(newDagFirstY T TM P Q)
  else (Node (Tip (Abs_trapez(topT T, bottomT T, leftP T, P)))
    (xNode P)
  (newDagFirstY T TM P Q) ))"
lemma newDagFirstNotSame[simp]: "newDagFirst T TM P Q \<noteq> Tip T"
  by (simp add: newDagFirst_def newDagFirstY_def)

(*gegebenes Trapez wird durch 2 neue Trapeze ersetzt; geteilt durch die Strecke PQ*)
definition newDagLastY :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
   "newDagLastY T TM P Q \<equiv> Node (Tip (Abs_trapez(topT T, (P,Q), topLeftCorner TM T P Q, Q)))
    (yNode (P,Q))
   (Tip (Abs_trapez((P,Q),bottomT T, bottomLeftCorner TM T P Q, Q)))"

(*Das letzte Trapez soll ersetzt werden, zu überprüfen ist ob Ecke im Trapez ist oder auf der Kante*)
definition newDagLast :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagLast T TM P Q \<equiv> (
  if (rightP T = Q) then(newDagLastY T TM P Q)
  else (Node (newDagLastY T TM P Q)
   (xNode Q)
  (Tip (Abs_trapez(topT T,bottomT T, Q, rightP T)))
  ))"
lemma newDagLastNotSame[simp]: "newDagLast T TM P Q \<noteq> Tip T"
  by (simp add: newDagLast_def newDagLastY_def)

(*Algorithm newDag(tDag,trapez, trapez list, segment)*)
(*Input: SuchBaum D, Trapez T das ersetz werden soll, Trapezliste TM mit Trapezen die Strecke PQ kreuzt, Strecke PQ(linksgeordnet)
Output: tDag welches Trapez T ersetzen soll*)
definition newDag :: "tDag \<Rightarrow> trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
"newDag D T TM P Q \<equiv> (if (length TM = 1) then (newDagSimp T P Q)
    else (if (queryTrapezoidMap D P = T) then (newDagFirst T TM P Q)
      else (if (queryTrapezoidMap D Q = T \<or> rightP T = Q) then (newDagLast T TM P Q)
        else (newDagM T TM P Q)
      )
    ))"
lemma newDagNotSame[simp]: "newDag D T TM P Q \<noteq> Tip T"
  by (simp add: newDag_def)




fun rUpNeighb :: "trapez list \<Rightarrow> trapez \<Rightarrow> trapez" where
  "rUpNeighb [] T = T"
  | "rUpNeighb (Tr#TN) T = (if(neighbor T Tr \<and> topT T = topT Tr)
    then (Tr) else (rUpNeighb TN T))"
lemma rUpNeighbElem[intro]:"(rUpNeighb TM T) \<in> set TM \<or> rUpNeighb TM T = T"
  by (induct TM T rule: rUpNeighb.induct, auto)
lemma rUpNeighbSimp: "rUpNeighb TM T = T \<or> (neighbor T (rUpNeighb TM T)
    \<and> topT (rUpNeighb TM T) = topT T)"
  by (induct TM, auto)
lemma rUpNeighbSimp1:"isTrapez T \<Longrightarrow> isTrapez (rUpNeighb (tDagList D) T) \<Longrightarrow>
  leftFrom (rightP T) (rightP (rUpNeighb (tDagList D) T)) \<or> rUpNeighb (tDagList D) T = T"
  by (meson neighbor_def rUpNeighbSimp trapezNeighbour1)

lemma rUpNeighbInDag[simp]:"tipInDag T D \<Longrightarrow>(rUpNeighb (tDagList D) T) \<in> set (tDagList D)"
  apply (induct "(tDagList D)" T rule: rUpNeighb.induct, auto)
  apply (metis tDagListNotEmpty)
using rUpNeighbElem tDagListComplete by fastforce

lemma rUpNeighbInDag1[simp]: "tipInDag (rUpNeighb (tDagList D) (queryTrapezoidMap D P)) D"
  apply (induct "tDagList D" "queryTrapezoidMap D P" rule: rUpNeighb.induct)
  apply (subgoal_tac "tipInDag (queryTrapezoidMap D P) D", simp)
  apply (auto)
by (auto simp add: tDagListComplete)

fun rBtNeighb :: "trapez list \<Rightarrow> trapez \<Rightarrow> trapez" where
  "rBtNeighb [] T = T"
  | "rBtNeighb (Tr#TN) T = (if(neighbor T Tr \<and> bottomT T = bottomT Tr)
    then (Tr) else (rBtNeighb TN T))"
lemma rBtNeighbElem[intro]:"(rBtNeighb TM T) \<in> set TM \<or> rBtNeighb TM T = T"
  by (induct TM T rule: rBtNeighb.induct, auto)
lemma rBtNeighbSimp: "rBtNeighb TM T = T 
  \<or> (neighbor T (rBtNeighb TM T) \<and> bottomT (rBtNeighb TM T) = bottomT T)"
  by (induct TM, auto)
lemma rBtNeighbSimp1:"isTrapez T \<Longrightarrow> isTrapez (rBtNeighb (tDagList D) T) \<Longrightarrow>
  leftFrom (rightP T) (rightP (rBtNeighb (tDagList D) T)) \<or> rBtNeighb (tDagList D) T = T"
  by (meson neighbor_def rBtNeighbSimp trapezNeighbour1)

lemma rBtNeighbInDag[simp]:"tipInDag T D \<Longrightarrow>(rBtNeighb (tDagList D) T) \<in> set (tDagList D)"
  apply (induct "(tDagList D)" T rule: rBtNeighb.induct, auto)
  apply (metis tDagListNotEmpty)
using rBtNeighbElem tDagListComplete by fastforce

lemma rBtNeighbInDag1[simp]: "tipInDag (rBtNeighb (tDagList D) (queryTrapezoidMap D P)) D"
  apply (induct "tDagList D" "queryTrapezoidMap D P" rule: rBtNeighb.induct)
  apply (subgoal_tac "tipInDag (queryTrapezoidMap D P) D", simp)
  apply (auto)
by (auto simp add: tDagListComplete)

(*Definition für trapMap*)
definition vertexInTramMap :: "tDag \<Rightarrow> bool" where
  "vertexInTramMap D \<equiv> \<forall> T \<in> set (tDagList D). \<forall> P \<in> set (xDagList D).
  pointInTrapez T P \<longrightarrow> leftP T = P \<or> rightP T = P"
definition trapezodalMapNeighbor :: "tDag \<Rightarrow> bool" where
  "trapezodalMapNeighbor D \<equiv> \<forall> Q T. (pointInDag D Q \<and> tipInDag T D \<and> xCoord(rightP T) < xCoord Q)
  \<longrightarrow> (rBtNeighb (tDagList D) T \<noteq> T \<or> rUpNeighb (tDagList D) T \<noteq> T)"
definition NoIntersectInTramMap :: "tDag \<Rightarrow> bool" where
  "NoIntersectInTramMap D \<equiv> \<forall> A B. A \<in> set (yDagList D) \<and> B \<in> set (yDagList D) \<longrightarrow> 
  \<not>intersect (fst A) (snd A) (fst B) (snd B)"
definition isTramMap :: "tDag \<Rightarrow> bool" where
  "isTramMap D \<equiv> trapezList (tDagList D) \<and> pointsInTramMap D \<and> vertexInTramMap D
  \<and> trapezodalMapNeighbor D \<and> uniqueXCoord (xDagList D) \<and> NoIntersectInTramMap D"

lemma isTramMapRBox[simp]: "isTrapez X \<Longrightarrow> isTramMap (Tip X)"
  apply (auto simp add: isTramMap_def pointInDag_def pointInTrapez_def trapezList_def)
  apply (auto simp add: pointsInTramMap_def vertexInTramMap_def NoIntersectInTramMap_def)
  apply (auto simp add: trapezodalMapNeighbor_def)
  apply (meson not_less pointInTrapezSimp)
done

lemma isTramMapNextTrapez[simp]: "isTramMap D \<Longrightarrow>
  pointInDag D Q \<Longrightarrow> tipInDag T D \<Longrightarrow> xCoord(rightP T) < xCoord Q \<Longrightarrow> rBtNeighb (tDagList D) T = T
  \<Longrightarrow> leftFrom (rightP T) (rightP (rUpNeighb (tDagList D) T))"
  apply (subgoal_tac "isTrapez (rUpNeighb (tDagList D) T)")
  apply (case_tac D, simp)
  apply (smt isTramMap_def rBtNeighb.simps(2) rUpNeighb.simps(1) rUpNeighb.simps(2)
    tDagList.simps(1) tipInDag.simps(1))
  apply (simp add: isTramMap_def)
sorry
lemma isTramMapNextTrapez1[simp]: "isTramMap D \<Longrightarrow> pointInDag D Q \<Longrightarrow> tipInDag T D \<Longrightarrow>
  xCoord(rightP T) < xCoord Q \<Longrightarrow> rUpNeighb (tDagList D) T = T \<Longrightarrow>
  leftFrom (rightP T) (rightP (rBtNeighb (tDagList D) T))"
  apply (case_tac D, simp)
sorry

(*lemma tramMap_measure_size [measure_function]:"isTramMap D \<and> pointInDag D Q \<Longrightarrow>
  leftFrom (rightP T) ()"*)
(*gib eine trapezliste, die on PQ geschnitten werden.*)
function followSegment :: "tDag \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  (*signedArea P Q (rightP T) \<noteq> 0 \<Longrightarrow> kann man beweisen, da PQ nicht durch rightP T durchgeht,
    und P Q nicht vollständig in T ist*)
  "followSegment D T P Q =
  (if (trapezodalMapNeighbor D \<and> pointInDag D Q \<and> leftFrom P Q) then (
    (if (xCoord (rightP T) < xCoord Q) then
      (if (leftTurn P Q (rightP T))
        then (T # followSegment D (rBtNeighb (tDagList D) T) P Q)
        else (T # followSegment D (rUpNeighb (tDagList D) T) P Q))
    else([T])))
   else ([]))"
by pat_completeness auto
termination followSegment
 (*apply (subgoal_tac "leftFrom ab b")*)
 apply (relation "measure (\<lambda> (D,T,P,Q). length (filter (\<lambda>x. xCoord(rightP T) \<le> x \<and> x \<le> xCoord Q)
   (map (xCoord o rightP)(tDagList D))))")
 apply (simp)
 (*beweise das das nächste Trapez rechts von dem linkem Trapez
  bzw. dass der Abstand zwischen rightP T und Q immer kleiner wird.
  Beweis mit Abstand für reale Zahlen garnicht möglich!
  Abstand kan beliebig klein werden und Q nicht erreichen
  Beweis sollte über die Anzahl der Elemente in der Liste sein, die noch als Nachbar in Frage kommen*)
sorry

(*alle Trapeze aus followSegment sind aus D*)
lemma followSegmetInDag[simp]:"tipInDag T D \<Longrightarrow> A \<in> set (followSegment D T P Q) \<Longrightarrow>
  A \<in> set (tDagList D)"
  apply (induct D T P Q rule: followSegment.induct, auto)
  apply (simp add: conflictingLeftTurns3 set_ConsD tDagListComplete)
  apply (simp add: pointInDag_def set_ConsD tDagListComplete)
by (smt empty_iff followSegment.simps insert_iff list.set(1) list.set(2) notLeftTurn notRightTurn1)
lemma followSegmetInDag1: "A \<in> set (followSegment D (queryTrapezoidMap D P) P Q) \<Longrightarrow> tipInDag A D"
  using followSegmetInDag queryTrapezoidMapInDag tDagListComplete by blast


(*gib eine trapezliste, die on PQ geschnitten werden.*)
definition intersectedTrapez :: "tDag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "leftFrom P Q \<Longrightarrow> intersectedTrapez D P Q \<equiv> followSegment D (queryTrapezoidMap D P) P Q"
lemma intersectedTrapezNotEmpty[simp]: "leftFrom p q \<Longrightarrow> rBoxTrapezS [p,q] R \<Longrightarrow>
  intersectedTrapez (Tip R) p q = [] \<Longrightarrow> False"
  apply (simp add: intersectedTrapez_def)
  apply (subgoal_tac "trapezodalMapNeighbor (Tip R) \<and> pointInDag (Tip R) q", simp)
  apply (subgoal_tac "xCoord (rightP R) \<ge> xCoord q", simp)
  apply (metis list.distinct(1))
  apply (auto) defer
  using pointInDag_def pointInRBox apply auto[1]
using isTramMapRBox isTramMap_def rBoxTrapezS_def by blast
(*jedes Trapez von intersectedTrapez ist aus D*)
lemma intersectedTrapezInDag[simp]: "leftFrom P Q \<Longrightarrow> T \<in> set (intersectedTrapez D P Q) \<Longrightarrow>
  tipInDag T D"
  by(auto simp add: intersectedTrapez_def, simp add: followSegmetInDag1)
(*enthält D nur eine rBox liefert intersectedTrapez nur die rBox*)
lemma intersectedTrapezSimp[simp]: "leftFrom p q \<Longrightarrow> rBoxTrapezS [p,q] R \<Longrightarrow>
  intersectedTrapez (Tip R) p q = [R]"
  apply (simp only: intersectedTrapez_def)
  apply (subgoal_tac "queryTrapezoidMap (Tip R) p = R")
  apply (erule ssubst)
  apply (subgoal_tac "xCoord (rightP R) \<ge> xCoord q", auto)
  using isTramMapRBox isTramMap_def rBoxTrapezS_def apply blast
  using pointInDag_def pointInRBox  apply auto[1]
  using pointInRBox pointInTrapez_def apply auto[1]
by (meson rBoxTrapezS_def list.set_intros(1) list.set_intros(2))
lemma intersectedTrapezSimp1[simp]: "isTrapez R \<Longrightarrow> leftFrom p q \<Longrightarrow> pointInDag (Tip R) p \<Longrightarrow>
  pointInDag (Tip R) q \<Longrightarrow> intersectedTrapez (Tip R) p q = [R]"
  apply (simp only: intersectedTrapez_def)
  apply (subgoal_tac "queryTrapezoidMap (Tip R) p = R")
  apply (erule ssubst)
  apply (subgoal_tac "xCoord (rightP R) \<ge> xCoord q")
  apply (smt followSegment.simps isTramMapRBox isTramMap_def)
by (auto simp add: pointInTrapez_def)

(*das erste Trapez enthält die linke Ecke*)
lemma intersectedHD[simp]: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  TM = intersectedTrapez D P Q \<Longrightarrow> hd(TM) = queryTrapezoidMap D P"
by (simp add: intersectedTrapez_def isTramMap_def)
(*das letzte Trapez enthält die letzte Ecke*)
lemma intersectedLast[intro]: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  TM = intersectedTrapez D P Q \<Longrightarrow> last(TM) = queryTrapezoidMap D Q
  \<or> leftP (queryTrapezoidMap D Q) = rightP (last TM)"
  apply (auto, simp only: intersectedTrapez_def)
sorry

(*segment ist im Trapez dann liefert intersectedTrapez nur ein Trapez*)
lemma intersectOne: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  TM = intersectedTrapez D P Q \<Longrightarrow> queryTrapezoidMap D Q = queryTrapezoidMap D P \<Longrightarrow> length TM = 1"
  apply (auto, simp only: intersectedTrapez_def)
  apply (simp)
  apply (subgoal_tac "xCoord (rightP (queryTrapezoidMap D P)) \<ge> xCoord Q", simp)
using isTramMap_def pointsInTramMap_def by auto
lemma intersectOne1:"isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  TM = intersectedTrapez D P Q \<Longrightarrow> pointInTrapez T P \<Longrightarrow> pointInTrapez T Q \<Longrightarrow> TM = [T]"
  apply (auto, simp only: intersectedTrapez_def)
  apply (subgoal_tac "xCoord (rightP (queryTrapezoidMap D P)) \<ge> xCoord Q", simp)
oops

(*segmet schneidet mehrere Trapeze, intersectedTrapez berechnet folge von benachbarten Trapezen*)
lemma intersectedTrapezComp: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  TM = intersectedTrapez D P Q \<Longrightarrow> (\<forall> i < length TM - 1. neighborAlongSeg (TM!i) (TM!Suc i) P Q)"
sorry





(*ersetzt alle übergebenen Trapeze im tDag durch neue Trapeze, die mit PQ erstellt wurden
Input : suchBaum D, 2 mal Liste mit Trapezen die ersetzt werden sollen,Segment PQ
Output: neues Dag, nachdem alle Trapeze ersetzt wurden*)
fun replaceDag :: "tDag \<Rightarrow> trapez list \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "replaceDag D [] _ _ _ = D"
  | "replaceDag D (T#Ts) TM P Q = replaceDag (replaceTip T (newDag D T TM P Q ) D) Ts TM P Q"

lemma replaceRBoxNotSame[simp]:"leftFrom p q \<Longrightarrow> rBoxTrapezS [p,q] R \<Longrightarrow>
  replaceDag (Tip R) (intersectedTrapez (Tip R) p q) (intersectedTrapez (Tip R) p q) p q \<noteq> Tip R"
by (simp)

(******add Segment to trapezoidal-map*)
(*erneure tDag nach dem hinzufügen eines segments*)
definition addSegmentToTrapezoidalMap :: "tDag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "leftFrom P Q \<Longrightarrow> addSegmentToTrapezoidalMap D P Q \<equiv>
    replaceDag D(intersectedTrapez D P Q)(intersectedTrapez D P Q) P Q"
lemma addSegmentsToRBoxNotSame [simp]:"leftFrom p q \<Longrightarrow> rBoxTrapezS [p,q] R \<Longrightarrow>
  addSegmentToTrapezoidalMap (Tip R) p q \<noteq> Tip R"
  apply (simp add: addSegmentToTrapezoidalMap_def)
done
lemma addSegmentsToRBox: "leftFrom p q \<Longrightarrow> rBoxTrapezS [p,q] R \<Longrightarrow>
  addSegmentToTrapezoidalMap (Tip R) p q = Node(Tip (Abs_trapez (topT R,bottomT R, leftP R, p)))(xNode p)
  (Node(Node(Tip (Abs_trapez(topT R,(p,q),p,q)))(yNode (p,q))(Tip (Abs_trapez((p,q),bottomT R, p, q))))
  (xNode q)(Tip (Abs_trapez (topT R,bottomT R, q, rightP R))))"
  apply (simp add: addSegmentToTrapezoidalMap_def newDag_def newDagSimp_def)
oops

lemma trapMapAfterAddSegment: "leftFrom P Q \<Longrightarrow> pointInDag T P \<Longrightarrow> pointInDag T Q \<Longrightarrow>
  T = replaceDag D(intersectedTrapez D P Q)(intersectedTrapez D P Q) P Q \<Longrightarrow>
  \<forall> a. pointInDag T a \<longrightarrow> pointInTrapez (queryTrapezoidMap T a) a"
sorry

(*keine Ecke aus dem Polygon ist im Trapez*)
lemma vertexInSimpTrapezoidalMap1: "leftFrom P Q \<Longrightarrow> rBoxTrapezS [P,Q] R \<Longrightarrow>
  D = addSegmentToTrapezoidalMap (Tip R) P Q \<Longrightarrow> \<not>pointInTrapezInner ((tDagList D)!i) (P)
  \<and> \<not>pointInTrapezInner ((tDagList D)!i) (Q)"
oops

(*wenn a in einem Trapez, dann ist a in einem der neuem Trapeze nach dem ein Segment
in trapezoidalMap aufgenommen wird*)
lemma "leftFrom P Q \<Longrightarrow> rBoxTrapezS [P,Q,a] R \<Longrightarrow> D =(addSegmentToTrapezoidalMap (Tip R) P Q)
  \<Longrightarrow> (\<exists> i < length (tDagList D). pointInTrapez ((tDagList D)!i) a)"
  (*apply (simp add: addSegmentToTrapezoidalMap_def intersectedTrapez_def)
  apply (subgoal_tac "\<not>neighborAlongSeg R R P Q", simp, thin_tac "\<not>neighborAlongSeg R R P Q")
  apply (simp add: newDag_def newDagSimp_def)
  apply (subgoal_tac "leftP R \<noteq> P \<and> rightP R \<noteq> Q", simp add: newDagSimpQ_def newDagSimpA_def)
  apply (thin_tac "leftP R \<noteq> P \<and> rightP R \<noteq> Q")
  apply (simp add: rBoxTrapezS_def pointInRBox_def, erule_tac x=2 in allE, simp)
  apply (case_tac "xCoord a < xCoord P")
    apply (rule_tac x=0 in exI, simp add: pointInTrapez_def, auto)
    apply (auto simp add: leftFrom_def less_eq_real_def conflictingRigthTurns1 not_le rightTurn_def)
  apply (case_tac "xCoord Q < xCoord a")
    apply (rule_tac x=3 in exI, simp add: pointInTrapez_def, auto)
  apply (case_tac "signedArea P Q a > 0")
    apply (rule_tac x=1 in exI, simp add: pointInTrapez_def)
  apply (rule_tac x=2 in exI, simp add: pointInTrapez_def, auto)
  (*proof for Subgoals*)
  apply (simp add: rBoxTrapezS_def, erule_tac x=0 in allE, safe, simp add: pointInRBox_def)
  apply (metis leftFrom_def less_irrefl)
  apply (simp add: rBoxTrapezS_def, erule_tac x=1 in allE, safe,simp, (simp add: pointInRBox_def))
  apply (metis leftFrom_def less_irrefl)
  apply (simp add: rBoxTrapezS_def)
done*)
oops

definition segmentCompWithDag :: "tDag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<equiv> pointInDag D P \<and> pointInDag D Q
  \<and> uniqueXCoord (xDagList D @ [P,Q]) \<and> (\<forall> A \<in> set (yDagList D). \<not>intersect (fst A) (snd A) P Q)"
lemma segmentAndDagUnicX[simp]:"isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  uniqueXCoord (xDagList D @ [P, Q])"
  by (simp add: isTramMap_def segmentCompWithDag_def)
lemma segmentAndDagUnicX1[simp]:"isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  uniqueXCoord (xDagList D @ [P])"
  using segmentAndDagUnicX uniqueXCoordAppend1 by blast
lemma segmentAndDagUnicX2[simp]:"isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  uniqueXCoord (xDagList D @ [Q])"
  using segmentAndDagUnicX uniqueXCoordAppend2 by blast


lemma addSegmentTrapezList: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow> trapezList (tDagList (addSegmentToTrapezoidalMap D P Q))"
sorry

(***unicX für newDagSimp*********)
lemma unicXSimpA [simp]: "segmentCompWithDag (Tip x) P Q \<Longrightarrow>
  uniqueXCoord (xDagList (newDagSimpA x P Q))"
  by (simp add: newDagSimpA_def)
lemma unicXSimp[simp]: "isTrapez x \<Longrightarrow> segmentCompWithDag (Tip x) P Q \<Longrightarrow>
  uniqueXCoord (xDagList (newDagSimp x P Q))"
  by (simp add: newDagSimp_def segmentCompWithDag_def newDagSimpA_def newDagSimpQ_def)
lemma unicXSimp1[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  uniqueXCoord (xDagList (newDagSimp x P Q))"
  apply (auto simp add: newDagSimp_def segmentCompWithDag_def newDagSimpA_def newDagSimpQ_def)
using uniqueXCoordAppend by blast
lemma uniqueXInNewDagSimp[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  uniqueXCoord (xDagList D @ xDagList (newDagSimp T P Q))"
  by(auto simp add: newDagSimp_def newDagSimpQ_def newDagSimpA_def isTramMap_def)

(***unicX für newDag*********)
lemma unicXFirst[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  uniqueXCoord (xDagList (newDagFirst a TM P Q))"
by (auto simp add: newDagFirst_def newDagFirstY_def)
lemma unicXLast[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  uniqueXCoord (xDagList (newDagLast a TM P Q))"
by (auto simp add: newDagLast_def newDagLastY_def)
lemma unicXnewDag[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
  uniqueXCoord (xDagList (newDag D a TM P Q))"
by (auto simp add: newDag_def newDagM_def)
lemma uniqueXInNewDagFirst[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
    uniqueXCoord (xDagList D @ xDagList (newDagFirst a TM P Q))"
   by (auto simp add: newDagFirst_def newDagFirstY_def isTramMap_def)
lemma uniqueXInNewDagLast[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
    uniqueXCoord (xDagList D @ xDagList (newDagLast a TM P Q))"
    by (auto simp add: newDagLast_def newDagLastY_def isTramMap_def)
lemma uniqueXInNewDagM[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow>
    uniqueXCoord (xDagList D @ xDagList (newDagM a TM P Q))"
    by (auto simp add: newDagM_def isTramMap_def)                                           
lemma uniqueXInNewDag[simp]: "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow> 
  uniqueXCoord (xDagList D @ xDagList (newDag D T TM P Q))"
  by (auto simp add: newDag_def)



lemma "isTramMap D \<Longrightarrow> segmentCompWithDag D P Q \<Longrightarrow> 
  uniqueXCoord (xDagList (replaceTip T (newDag D T TM P Q) D))"
  apply (subgoal_tac "\<forall> a \<in> set(xDagList(replaceTip T (newDag D T TM P Q) D)). a \<in> set(xDagList D)
    \<or> a \<in> set( xDagList (newDag D T TM P Q))\<longrightarrow> 
    uniqueXCoord (xDagList (replaceTip T (newDag D T TM P Q) D))", auto) defer
  
  

  apply (case_tac "(T, newDag D T TM P Q, D)" rule: replaceTip.cases)
  apply (simp) using unicXnewDag apply auto[1]
  apply (simp) using unicXnewDag apply auto[1]
  

  apply (induct T "newDag D T TM P Q" D rule: replaceTip.induct)
  apply (simp) using unicXnewDag apply auto[1]
  apply (simp)

lemma "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow> \<forall> a \<in> set (TM::(trapez list)). tipInDag a D \<Longrightarrow> 
  uniqueXCoord (xDagList (replaceDag D TM TM P Q))"
  apply (auto simp add: uniqueXCoord_def)
  apply (induct "replaceDag D TM TM P Q" rule: xDagList.induct) defer
  apply (simp)

  apply (induct D TM TM P Q rule: replaceDag.induct) defer
  apply (simp)

lemma addSegmentsUnicX: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow> uniqueXCoord (xDagList (addSegmentToTrapezoidalMap D P Q))"
  apply (simp add: addSegmentToTrapezoidalMap_def)
  apply (induct D "intersectedTrapez D P Q" "intersectedTrapez D P Q" P Q rule: replaceDag.induct)
  apply (simp add: isTramMap_def)


  apply (induction "intersectedTrapez D P Q")
  apply (simp add: newDag_def, simp add: isTramMap_def trapezList_def)
  apply (simp)
  apply (auto simp add: replaceDag.s)
  

  apply (induct_tac "intersectedTrapez (D1 x2 D2) P Q" "intersectedTrapez (D1 x2 D2) P Q" P Q rule: replaceDag.induct)
  apply (simp add: isTramMap_def)
oops


lemma addSegmentPointsInMap: "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow> pointsInTramMap (addSegmentToTrapezoidalMap D P Q)"
  apply (simp add: addSegmentToTrapezoidalMap_def)
oops

theorem "isTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  segmentCompWithDag D P Q \<Longrightarrow> isTramMap (addSegmentToTrapezoidalMap D P Q)"
  apply (simp add: addSegmentToTrapezoidalMap_def)
oops





(*****Add Polygon to trapezoidal-map*)
(*Input: List of line segments(one Polygon) forming a planar subdivision.
Output:  A trapezoid map M in associated search structure tDag.*)
fun addSegmentsToTrapezoidalMap :: "tDag \<Rightarrow> point2d list \<Rightarrow> tDag" where
  "addSegmentsToTrapezoidalMap D [] = D"
  | "addSegmentsToTrapezoidalMap D [p] = D"
  | "addSegmentsToTrapezoidalMap D (p#q#xs) = addSegmentsToTrapezoidalMap
    (addSegmentToTrapezoidalMap D (leftPSegment p q) (rightPSegment p q)) (q#xs)"

(*füge Segment in tDag ein, wenn tDag \<noteq> rBox*)
(*jedes a was in rBox ist, ist auch nach dem Hinzufügen von einem Polygon in einem der Trapeze
zu finden*)
lemma addPolygonToRBox: "uniqueXCoord L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow>
  rBoxTrapezS L R \<Longrightarrow> D = addSegmentsToTrapezoidalMap (Tip R) P \<Longrightarrow> rBoxTrapezS [a] R \<Longrightarrow>
  \<exists> i < length (tDagList D). pointInTrapez ((tDagList D)!i) a"
oops

(*jede Ecke des Polygons ist entweder eine ecke eines Trapezes oder garnicht im Trapez*)
lemma "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> uniqueXCoord L \<Longrightarrow> rBoxTrapezS P R \<Longrightarrow>
  T \<in> set (tDagList (addSegmentsToTrapezoidalMap (Tip R) P)) \<Longrightarrow> a \<in> set P \<Longrightarrow>
  pointInTrapez T a \<longrightarrow> leftP T = a \<or> rightP T = a"
  apply (simp)
  apply (induction "Tip R" P rule: addSegmentsToTrapezoidalMap.induct)
  apply (simp add: cyclePath_def) using cyclePath_def apply auto[1]
  apply (auto)
  apply (subgoal_tac "addSegmentsToTrapezoidalMap (Tip R) (cyclePath L) = addSegmentsToTrapezoidalMap
    (addSegmentToTrapezoidalMap (Tip R) (leftPSegment p q) (rightPSegment p q)) (q#xs)") defer
  apply (metis addSegmentsToTrapezoidalMap.simps(3))
  apply (simp)
  apply (thin_tac "addSegmentsToTrapezoidalMap (Tip R) (cyclePath L) =
       addSegmentsToTrapezoidalMap
        (addSegmentToTrapezoidalMap (Tip R) (leftPSegment p q) (rightPSegment p q)) (q # xs)")
  apply (case_tac "leftFrom p q", subgoal_tac "p = leftPSegment p q",
    subgoal_tac "q = rightPSegment p q") defer
    apply (simp, simp) defer
  apply (simp add: addSegmentToTrapezoidalMap_def)
  apply (subgoal_tac "replaceDag (Tip R) (intersectedTrapez (Tip R) p q) (intersectedTrapez (Tip R) p q) p q \<noteq> Tip R") defer
apply (metis list.distinct(1) list.set_cases list.set_intros(1) list.set_intros(2) rBoxTrapezS_def replaceRBoxNotSame set_ConsD) defer
  apply (simp)
  apply (thin_tac "replaceDag (Tip R) (intersectedTrapez (Tip R) p q) (intersectedTrapez (Tip R) p q) p q \<noteq> Tip R")
  
oops
(*keine Ecke aus dem Polygon ist im Trapez*)
lemma vertexInSimpTrapezoidalMap: "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow>
  uniqueXCoord L \<Longrightarrow> rBoxTrapezS L R \<Longrightarrow> D = addSegmentsToTrapezoidalMap (Tip R) P \<Longrightarrow> 
  i < length (tDagList D) \<Longrightarrow> k < length P \<Longrightarrow> \<not>pointInTrapezInner ((tDagList D)!i) (P!k)"
  apply (simp)
  apply (induction "Tip R" P rule: addSegmentsToTrapezoidalMap.induct)
  apply (simp add: cyclePath_def) using cyclePath_def apply auto[1]
  apply (simp)
oops

(*wenn ein Ecke aus dem Polygon im Trapez, dann ist es der leftP/rightP*)
lemma vertexInSimpTrapezoidalMap: "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow>
  uniqueXCoord L \<Longrightarrow> rBoxTrapezS L R \<Longrightarrow> D = addSegmentsToTrapezoidalMap (Tip R) P \<Longrightarrow> 
  i < length (tDagList D) \<Longrightarrow> k < length P \<Longrightarrow> pointInTrapez ((tDagList D)!i) (P!k) \<Longrightarrow>
  leftP ((tDagList D)!i) = P!k \<or> rightP ((tDagList D)!i) = P!k"
  apply (simp)
  apply (cases "((Tip R), P)" rule: addSegmentsToTrapezoidalMap.cases)
  apply (simp add: cyclePath_def) using cyclePath_def apply auto[1]
  apply (simp)
oops

fun addSegmentListToTrapezoidalMap :: "tDag \<Rightarrow> (point2d list) list \<Rightarrow> tDag" where
   "addSegmentListToTrapezoidalMap D [] = D"
  | "addSegmentListToTrapezoidalMap D (x#xs) = addSegmentListToTrapezoidalMap
    (addSegmentsToTrapezoidalMap D x) xs"


(*jedes a was in rBox ist, ist auch nach dem Hinzufügen von mehreren Polygonen in einem der
Trapeze zu finden*)
lemma buildTrapezoidalMap: "polygonList PL\<Longrightarrow> \<not>cyclePathsIntersect PL\<Longrightarrow> uniqueXCoord (concat PL)
  \<Longrightarrow> rBoxTrapezS (concat PL) R \<Longrightarrow> D = addSegmentListToTrapezoidalMap (Tip R) PL \<Longrightarrow>
  rBoxTrapezS [a] R \<Longrightarrow> \<exists> i < length (tDagList D). pointInTrapez ((tDagList D)!i) a"
oops

(*wenn ein Ecke aus der Polygonen-Liste im Trapez, dann ist es der leftP/rightP*)
lemma vertexInBuildTrapezoidalMap: "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow>
  rBoxTrapezS (concat PL) R \<Longrightarrow> polygonsDisjoint PL \<Longrightarrow> D = addSegmentListToTrapezoidalMap (Tip R) PL \<Longrightarrow> 
  i < length (tDagList D) \<Longrightarrow> k < length PL \<Longrightarrow> pointInTrapezInner ((tDagList D)!i) ((concat PL)!k) \<Longrightarrow>
  (leftP ((tDagList D)!i) = (concat PL)!k \<or> rightP ((tDagList D)!i) = (concat PL)!k)"
  (*apply (simp)
  apply (cases "((Tip R), PL)" rule: addSegmentListToTrapezoidalMap.cases, simp)
  apply (simp)
  apply (metis Suc_eq_plus1 add.left_neutral add_diff_cancel_right cyclePathAdjacentSame
    cyclePath_def diff_zero hd_append last_conv_nth last_snoc length_0_conv length_Cons
    length_append list.sel(1) neq0_conv neq_Nil_conv nth_Cons_0 pointLists_def prod.sel(2))
  
 thm vertexInSimpTrapezoidalMap
  apply (cut_tac L=P and P="(cyclePath P)" and R=R in vertexInSimpTrapezoidalMap)*)
sorry

(*keine der Ecken aus der Polygon-Liste ist im Trapez, außer der Trapez-Ecken*)
lemma vertexInTrapez: "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow>
  rBoxTrapezS (concat PL) R \<Longrightarrow> polygonsDisjoint PL \<Longrightarrow>
  D = addSegmentListToTrapezoidalMap (Tip R) PL \<Longrightarrow>  i < length (tDagList D) \<Longrightarrow> k < length PL \<Longrightarrow>
  \<not>pointInTrapezInner ((tDagList D)!i) ((concat PL)!k) \<or> leftP ((tDagList D)!i) = (concat PL)!k
  \<or> rightP ((tDagList D)!i) = (concat PL)!k"
by (simp add: vertexInBuildTrapezoidalMap)



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



(*alte Definition*)
(*(*gib den nächsten Nachbarn von einem Trapez folgend der Strecke PQ  aus der Trapez-Liste
Input: tDag, tDagList geordnet nach der x-Coordinate von leftP, Strecke PQ
Output: nächster trapez-Nachbar, wenn man PQ folgt*)
(*es muss ein Nachbar geben! kein Nachbar wird ausgelassen!*)
fun nextTrapez :: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez" where
  "nextTrapez [] T _ _ = T"
  | "nextTrapez (Ts#Tm) T P Q = (if(neighborAlongSeg T Ts (leftPSegment P Q) (rightPSegment P Q))
  then(Ts) else(nextTrapez Tm T P Q))"
lemma "leftFrom P Q \<Longrightarrow> nextTrapez (tDagList D) T P Q = T
    \<or> neighbor T (nextTrapez (tDagList D) T P Q)"
  apply (auto)
  apply (induct "(tDagList D)" T P Q rule:nextTrapez.induct, simp+)
  apply (subgoal_tac "P = leftPSegment P Q \<and> Q=rightPSegment P Q")
  apply (auto simp add:  )
lemma trapMapRightmost:"(rightP T) = (rightP (nextTrapez (tDagList D) T P Q)) \<Longrightarrow>
  nextTrapez (tDagList D) T P Q = last (tDagList D)"
oops
(*The termination argument for followS is based on the fact that the difference
between "xCoord (rightP T)" and  "xCoord Q"  gets smaller in every step*)
lemma "\<forall>a. pointInDag y a \<longrightarrow> pointInTrapez (queryTrapezoidMap y a) a \<Longrightarrow> 
  rightP T \<noteq> rightP (nextTrapez (tDagList y) T P Q) \<Longrightarrow>
  leftFrom (rightP T) (rightP (nextTrapez (tDagList y) T P Q))"
  apply (induct "tDagList y" T P Q rule: nextTrapez.induct, auto)
oops
lemma tramMap_measure_size [measure_function]: "leftFrom (rightP T)
 (rightP (nextTrapez (tDagList D) T P Q))
 \<or> (rightP T) = (rightP (nextTrapez (tDagList D) T P Q))"
 apply (case_tac D, auto)
 apply (case_tac "leftFrom P Q", subgoal_tac "P = leftPSegment P Q \<and> Q = rightPSegment P Q")
  apply (simp, simp add: neighborAlongSeg_def, simp)
  apply (subgoal_tac "leftFrom Q P \<and> Q = leftPSegment P Q \<and> P = rightPSegment P Q")
  apply (simp add: neighborAlongSeg_def) defer
 apply (case_tac "leftFrom P Q", subgoal_tac "P = leftPSegment P Q \<and> Q = rightPSegment P Q")
 apply (simp)
 apply (induct "tDagList x1" T P Q rule: nextTrapez.induct)
oops*)


(*definition pointOnList :: "real list \<Rightarrow> real \<Rightarrow> bool" where
  "pointOnList L P \<equiv> \<exists>x\<in>set L. P < x"
fun nextPoint :: "real list \<Rightarrow> real \<Rightarrow> real" where
  "nextPoint (X#Ls) P = (if (X > P)
    then (X)
    else (nextPoint Ls P))"

lemma foo: "pointOnList P A \<Longrightarrow> A < (nextPoint P A)"
  apply (induct P A rule: nextPoint.induct)
by (auto simp add: pointOnList_def)+

lemma bla: "pointOnList L P  \<Longrightarrow> A = nextPoint L P \<Longrightarrow> length [ P < A] < length L"sorry
sorry
lemma bla1: "pointOnList L P \<Longrightarrow>
  ((L, nextPoint L P), L, P) \<in> measure (\<lambda>(L, P). length (filter (op < P) L))"
  apply (auto)
sorry
function listBetween :: "real list \<Rightarrow> real \<Rightarrow> real \<Rightarrow> real list" where
  "pointOnList L P \<Longrightarrow> pointOnList L Q \<Longrightarrow> listBetween L P Q = (if(P \<le> Q)
  then(P # (listBetween L (nextPoint L P) Q))
  else([]))"
  apply (auto)
sorry
termination listBetween
  apply (relation "measure (\<lambda> (L,P,Q). length (filter (\<lambda>x. P \<le> x \<and> x \<le> Q) L))")
  apply (simp, simp)
  (*apply (relation "measure (\<lambda> (L,P,Q). length [ A \<leftarrow> L. P < A])")
  apply clarsimp
  apply (subgoal_tac "((L, nextPoint L P), L, P) \<in> measure (\<lambda>(L, P). length (filter (op < P) L))")
  apply (simp)
using bla1 by blast*)*)
end
