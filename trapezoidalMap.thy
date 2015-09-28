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
lemma queryTrapezoidMapInDag: "tipInDag (queryTrapezoidMap D P) D"
  apply (subgoal_tac "(queryTrapezoidMap D P) \<in> set (tDagList D)", simp add: tDagListComplete)
by (induct D P rule: queryTrapezoidMap.induct, auto)
lemma pointInRBox1: "\<forall> a. pointInDag (Tip R) a \<longrightarrow>
  pointInTrapez (queryTrapezoidMap (Tip R) a) a"
  apply (auto, simp add: pointInDag_def)
done
lemma pointInRBox: "rBoxTrapezS PL R \<Longrightarrow> \<forall> a \<in> set PL.
  pointInTrapez (queryTrapezoidMap (Tip R) a) a"
  apply (auto)
  apply (auto simp add: rBoxTrapezS_def pointInTrapez_def)
  using leftFrom_def pointInRBox_def apply auto[1]
  using leftFrom_def pointInRBox_def apply auto[1]
  using pointInRBox_def rightTurn_def apply fastforce
  using pointInRBox_def rightTurn_def apply fastforce
done

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
lemma newDagSimpTrapez:"\<forall> a \<in> set (tDagList (newDagSimp R p q)). isTrapez (Rep_trapez a)"
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
lemma rUpNeighbSimp: "rUpNeighb TM T = T \<or> (neighbor T (rUpNeighb TM T)
    \<and> topT (rUpNeighb TM T) = topT T)"
  by (induct TM, auto)
lemma rUpNeighbSimp1:"leftFrom (rightP T) (rightP (rUpNeighb (tDagList D) T))
  \<or> rUpNeighb (tDagList D) T = T"
  using neighbor_def rUpNeighbSimp trapezNeighbour3 by blast
fun rBtNeighb :: "trapez list \<Rightarrow> trapez \<Rightarrow> trapez" where
  "rBtNeighb [] T = T"
  | "rBtNeighb (Tr#TN) T = (if(neighbor T Tr \<and> bottomT T = bottomT Tr)
    then (Tr) else (rBtNeighb TN T))"
lemma rBtNeighbSimp: "rBtNeighb TM T = T 
  \<or> (neighbor T (rBtNeighb TM T) \<and> bottomT (rBtNeighb TM T) = bottomT T)"
  by (induct TM, auto)
lemma rBtNeighbSimp1:"leftFrom (rightP T) (rightP (rBtNeighb (tDagList D) T))
  \<or> rBtNeighb (tDagList D) T = T"
  using neighbor_def rBtNeighbSimp trapezNeighbour3 by blast
(*in tDag müsste drin stecken, dass keine x-Koordinate von einem x-Node gleich ist.
Keines der y-Node sich schneide, außer die Ecken sind gleich (und was dann?)*)
definition isTramMap :: "tDag \<Rightarrow> bool" where
  "isTramMap D \<equiv> \<forall> Q T. (pointInDag D Q \<and> tipInDag T D \<and> xCoord(rightP T) < xCoord Q) \<longrightarrow>
    (rBtNeighb (tDagList D) T \<noteq> T \<or> rUpNeighb (tDagList D) T \<noteq> T)"
lemma isTramMapRBox: "isTramMap (Tip X)"
  by (auto simp add: isTramMap_def pointInDag_def pointInTrapez_def)

lemma isTramMapNextTrapez[simp]: "isTramMap D \<Longrightarrow> pointInDag D Q \<Longrightarrow> tipInDag T D \<Longrightarrow>
  xCoord(rightP T) < xCoord Q \<Longrightarrow> rBtNeighb (tDagList D) T = T \<Longrightarrow>
  leftFrom (rightP T) (rightP (rUpNeighb (tDagList D) T))"
  apply (case_tac D, simp)
  using isTramMap_def tDagList.simps(1) apply fastforce
  apply (simp add: isTramMap_def)
by (metis rUpNeighbSimp1 tDagList.simps(2))
lemma isTramMapNextTrapez1[simp]: "isTramMap D \<Longrightarrow> pointInDag D Q \<Longrightarrow> tipInDag T D \<Longrightarrow>
  xCoord(rightP T) < xCoord Q \<Longrightarrow> rUpNeighb (tDagList D) T = T \<Longrightarrow>
  leftFrom (rightP T) (rightP (rBtNeighb (tDagList D) T))"
  apply (case_tac D, simp)
  using isTramMap_def tDagList.simps(1) apply fastforce
  apply (simp add: isTramMap_def)
by (metis rBtNeighbSimp1 tDagList.simps(2))

(*lemma tramMap_measure_size [measure_function]:"isTramMap D \<and> pointInDag D Q \<Longrightarrow>
  leftFrom (rightP T) ()"*)
(*gib eine trapezliste, die on PQ geschnitten werden.*)
function followSegment :: "tDag \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  (*signedArea P Q (rightP T) \<noteq> 0 \<Longrightarrow> kann man beweisen, da PQ nicht durch rightP T durchgeht,
    und P Q nicht vollständig in T ist*)
  "followSegment D T P Q =
  (if (isTramMap D \<and> pointInDag D Q \<and> leftFrom P Q) then (
    (if (xCoord (rightP T) < xCoord Q) then
      (if (leftTurn P Q (rightP T))
        then (rUpNeighb (tDagList D) T # followSegment D (rBtNeighb (tDagList D) T) P Q)
      else (rBtNeighb (tDagList D) T # followSegment D (rUpNeighb (tDagList D) T) P Q))
      else((if (leftTurn P Q (rightP T))
        then ([rUpNeighb (tDagList D) T])
      else ([rBtNeighb (tDagList D) T])))))
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

(*gib eine trapezliste, die on PQ geschnitten werden.*)
definition intersectedTrapez :: "tDag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "leftFrom P Q \<Longrightarrow> intersectedTrapez D P Q \<equiv> followSegment D (queryTrapezoidMap D P) P Q"
lemma intersectedTrapezComp: "leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  TM = intersectedTrapez D P Q \<Longrightarrow> (\<forall> i < length TM - 1. neighborAlongSeg (TM!i) (TM!Suc i) P Q)
  \<and> (\<forall> i < length TM. tipInDag (TM!i) D)
  \<and> hd(TM) = queryTrapezoidMap D P \<and> last(TM) = queryTrapezoidMap D Q"
sorry
lemma intersectedTrapezNotEmpty[simp]: "leftFrom p q \<Longrightarrow> rBoxTrapezS [p,q] R \<Longrightarrow>
  intersectedTrapez (Tip R) p q = [] \<Longrightarrow> False"
  apply (simp add: intersectedTrapez_def)
  apply (subgoal_tac "isTramMap (Tip R) \<and> pointInDag (Tip R) q", simp)
  apply (subgoal_tac "xCoord (rightP R) \<ge> xCoord q", simp)
  apply (metis list.distinct(1))+
  apply (auto) defer
  using pointInDag_def pointInRBox apply auto[1]
using isTramMapRBox by blast

lemma intersectedTrapezSimp[simp]: "leftFrom p q \<Longrightarrow> rBoxTrapezS [p,q] R \<Longrightarrow>
  intersectedTrapez (Tip R) p q = [R]"
  apply (simp only: intersectedTrapez_def)
  apply (subgoal_tac "queryTrapezoidMap (Tip R) p = R")
  apply (erule ssubst)
  apply (subgoal_tac "xCoord (rightP R) \<ge> xCoord q")
  apply (auto simp add: isTramMapRBox)
  using pointInDag_def pointInRBox apply auto[1]
  using pointInDag_def pointInRBox apply auto[1]
  using pointInDag_def pointInRBox apply auto[1]
using pointInRBox pointInTrapez_def by auto[1]

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
  pointInTrapez T A \<longrightarrow> leftP T = a \<or> rightP T = a"
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
