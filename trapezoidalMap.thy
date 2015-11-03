theory trapezoidalMap
imports tDag polygon (*"~~/src/HOL/Library/Multiset"*)
begin

(*#######Suche nach Punkten in der Trapezoidal-Map#########*)

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
(*query gibt nur elemente von tDag zurück*)
lemma queryTrapezoidMapInDagList[simp]: "(queryTrapezoidMap D P) \<in> set (tDagList D)"
  using queryTrapezoidMapInDag tDagListComplete by blast
(*wenn tDagList nur echte Trapeze enthält ist queryTrapezoidMap auch ein echtes Trapez*)
lemma queryTrapezoidMapIsTrapez[simp]:"trapezList (tDagList D) \<Longrightarrow> isTrapez (queryTrapezoidMap D P)"
  using queryTrapezoidMapInDag tDagListComplete trapezList_def by blast

(*alle Punkte die in rBox liegen findet quiryTrapezoidMap*)
lemma pointInRBox1: "pointInDag (Tip R) a \<Longrightarrow> pointInTrapez (queryTrapezoidMap (Tip R) a) a"
  apply (auto, simp add: pointInDag_def)
done
lemma pointInRBox:"rBoxTrapezS PL R \<Longrightarrow> a \<in> set PL \<Longrightarrow>pointInTrapez (queryTrapezoidMap (Tip R) a) a"
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
(*rechte Ecke rechts von queryTrapezoidMap*)
lemma pointInQueryTrapezoid: "trapezList (tDagList D) \<Longrightarrow> pointsInTramMap D \<Longrightarrow> pointInDag D P \<Longrightarrow>
  xCoord P \<le> xCoord (rightP (queryTrapezoidMap D P))"
  using pointInTrapezSimp pointsInTramMap_def queryTrapezoidMapInDag tDagListComplete
  trapezList_def by blast

(*pointsInTramMap gilt für rBox*)
lemma rBoxPointsInTramMap: "isTrapez R \<Longrightarrow> pointsInTramMap (Tip R)"
  by (auto simp add: pointsInTramMap_def)




(*#######Konstruieren neuer Bäume beim hinzufügen neuer Strecken#########*)

(*****create new Dag to replace intersected Trapez*)
(*Einfacher Fall: allgemeinFall*)
definition newDagSimpA :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagSimpA T P Q \<equiv>
   Node (Tip (Abs_trapez (topT T,(P,Q),P,Q)))
    (yNode (P,Q))
   (Tip (Abs_trapez ((P,Q),bottomT T,P,Q)))"
lemma newDagSimpANotSame[simp]: "newDagSimpA T P Q \<noteq> Tip T"
  by (simp add: newDagSimpA_def)
lemma neDagSimpAIsTrapez [simp]:"leftFrom P Q \<Longrightarrow> isTrapez T \<Longrightarrow>
  trapezList (tDagList (newDagSimpA T P Q))"
  apply (auto simp add: newDagSimpA_def trapezList_def)
oops
  

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

(*newDagSimp konstruiert echtes Trapez*)
lemma newDagSimpTrapez:"\<forall> a \<in> set (tDagList (newDagSimp R p q)). isTrapez (a)"
  apply (auto simp add: newDagSimp_def newDagSimpQ_def newDagSimpA_def)
oops

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

(*newDag konstruiert ein Baum, für dessen x-Knoten uniqueXCoord gilt, wenn Strecke nicht vertikal*)
lemma unicXSimpA[simp]: "leftFrom P Q \<Longrightarrow> uniqueXCoord (xDagList (newDagSimpA D P Q))"
  by (simp add: newDagSimpA_def)
lemma unicXSimp[simp]: "leftFrom P Q \<Longrightarrow> uniqueXCoord (xDagList (newDagSimp D P Q))"
  by (auto simp add: newDagSimp_def newDagSimpA_def newDagSimpQ_def pointsUniqueXCoord)
lemma unicXFirst[simp]: "leftFrom P Q \<Longrightarrow> uniqueXCoord (xDagList (newDagFirst a TM P Q))"
  by (auto simp add: newDagFirst_def newDagFirstY_def)
lemma unicXLast[simp]: "leftFrom P Q \<Longrightarrow> uniqueXCoord (xDagList (newDagLast a TM P Q))"
  by (auto simp add: newDagLast_def newDagLastY_def)
lemma unicXnewDag[simp]: "leftFrom P Q \<Longrightarrow> uniqueXCoord (xDagList (newDag D a TM P Q))"
  by (auto simp add: newDag_def newDagM_def)

(*welche x-Knoten kann newDag enthalten*)
lemma xDagListNewDagSimpA [simp]:"xDagList (newDagSimpA T P Q) = []" by (simp add: newDagSimpA_def)
lemma xDagListNewDagSimp1[intro]:"xDagList (newDagSimp T P Q) = [P,Q]
  \<or> xDagList (newDagSimp T P Q) = [P] \<or> xDagList (newDagSimp T P Q) = []
  \<or> xDagList (newDagSimp T P Q) = [Q]"
  by (auto simp add: newDagSimp_def newDagSimpQ_def)
lemma xDagListNewDagM[simp]:"xDagList (newDagM T TM P Q) = []" by (auto simp add: newDagM_def)
lemma xDagListNewDagFirst[intro]:"xDagList (newDagFirst T TM P Q) = []
  \<or> xDagList (newDagFirst T TM P Q) = [P]"
  by (auto simp add: newDagFirst_def newDagFirstY_def)
lemma xDagListNewDagLast[intro]:"xDagList (newDagLast T TM P Q) = []
  \<or> xDagList (newDagLast T TM P Q) = [Q]"
  by (auto simp add: newDagLast_def newDagLastY_def)
lemma xDagListNewDag[intro]:"xDagList (newDag D T TM P Q) = [P,Q]
  \<or> xDagList (newDag D T TM P Q) = [P] \<or> xDagList (newDag D T TM P Q) = [Q]
  \<or> xDagList (newDag D T TM P Q) = []"
  apply (auto simp add: newDag_def newDagFirst_def newDagFirstY_def newDagLast_def newDagLastY_def)
  using xDagListNewDagSimp1 apply blast
  using xDagListNewDagSimp1 apply blast
using xDagListNewDagSimp1 by blast

(*welche y-Knoten kann newDag enthalten*)
lemma yDagListNewDagSimp[simp]: "yDagList (newDagSimp T P Q) = [(P,Q)]"
  by (auto simp add: newDagSimp_def newDagSimpQ_def newDagSimpA_def)
lemma yDagListNewDag[simp]: "yDagList (newDag D TM T P Q) = [(P,Q)]"
  by (auto simp add: newDag_def newDagM_def newDagFirst_def newDagFirstY_def
    newDagLast_def newDagLastY_def)





(*#######Suche nach Trapezen die von einer Strecke geschnitten werden#########*)

(*Such nach rechten oberen Trapeznachbar*)
fun rUpNeighb :: "trapez list \<Rightarrow> trapez \<Rightarrow> trapez" where
  "rUpNeighb [] T = T"
  | "rUpNeighb (Tr#TN) T = (if(neighbor T Tr \<and> topT T = topT Tr)
    then (Tr) else (rUpNeighb TN T))"
lemma rUpNeighbElem[intro]:"(rUpNeighb TM T) \<in> set TM \<or> rUpNeighb TM T = T"
  by (induct TM T rule: rUpNeighb.induct, auto)
lemma rUpNeigbIsTrapez:"trapezList TM \<Longrightarrow> isTrapez T \<Longrightarrow> isTrapez (rUpNeighb TM T)"
  by (induct TM T rule: rUpNeighb.induct, simp, simp add: trapezList_def)
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

(*Such nach rechten unteren Trapeznachbar*)
fun rBtNeighb :: "trapez list \<Rightarrow> trapez \<Rightarrow> trapez" where
  "rBtNeighb [] T = T"
  | "rBtNeighb (Tr#TN) T = (if(neighbor T Tr \<and> bottomT T = bottomT Tr)
    then (Tr) else (rBtNeighb TN T))"
lemma rBtNeighbElem[intro]:"(rBtNeighb TM T) \<in> set TM \<or> rBtNeighb TM T = T"
  by (induct TM T rule: rBtNeighb.induct, auto)
lemma rBtNeigbIsTrapez:"trapezList TM \<Longrightarrow> isTrapez T \<Longrightarrow> isTrapez (rBtNeighb TM T)"
  by (induct TM T rule: rBtNeighb.induct, simp, simp add: trapezList_def)
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

(*Definition für Bedingung der Nacharn. jedesmal wenn ein Punkt sich rechts von einem Trapez T
  befindet, muss es für T einen rechten Nachbar geben*)
definition trapezMapNeighbor :: "tDag \<Rightarrow> bool" where
  "trapezMapNeighbor D \<equiv> \<forall> Q T. (pointInDag D Q \<and> tipInDag T D \<and> xCoord(rightP T) < xCoord Q)
  \<longrightarrow> (rBtNeighb (tDagList D) T \<noteq> T \<or> rUpNeighb (tDagList D) T \<noteq> T)"
(*rBox entspricht der Definition von trapezMapNeigbor*)
lemma isRBoxMapNeighbor[simp]:"isTrapez X \<Longrightarrow> trapezMapNeighbor (Tip X)"
  apply (auto simp add: trapezMapNeighbor_def)
by (meson not_le pointInTrapezSimp)

(*position der Ecken des rechten Nachbar von T zu T*)
lemma isTramMapNextTrapez[simp]: "trapezMapNeighbor D \<Longrightarrow> trapezList (tDagList D) \<Longrightarrow>
  pointInDag D Q \<Longrightarrow> tipInDag T D \<Longrightarrow> xCoord(rightP T) < xCoord Q \<Longrightarrow> rBtNeighb (tDagList D) T = T
  \<Longrightarrow> leftFrom (rightP T) (rightP (rUpNeighb (tDagList D) T))"
  by (meson rUpNeighbInDag rUpNeighbSimp1 tDagListComplete trapezListTDag trapezMapNeighbor_def)
lemma isTramMapNextTrapez1[simp]: "trapezMapNeighbor D \<Longrightarrow> trapezList (tDagList D) \<Longrightarrow>
  pointInDag D Q \<Longrightarrow> tipInDag T D \<Longrightarrow> xCoord(rightP T) < xCoord Q \<Longrightarrow> rUpNeighb (tDagList D) T = T
  \<Longrightarrow> leftFrom (rightP T) (rightP (rBtNeighb (tDagList D) T))"
  by (meson rBtNeighbInDag rBtNeighbSimp1 tDagListComplete trapezListTDag trapezMapNeighbor_def)

(*Beweis für die Termination von followSeg*)
lemma nextNeighbour: "trapezMapNeighbor D \<Longrightarrow> trapezList (tDagList D) \<Longrightarrow> tipInDag T D \<Longrightarrow>
  length (filter ((\<lambda>x. xCoord (rightP (rBtNeighb (tDagList D) T)) < x) \<circ> (xCoord \<circ> rightP))
          (tDagList D))
  < length (filter ((\<lambda>x. xCoord (rightP T) < x) \<circ> (xCoord \<circ> rightP)) (tDagList D))"
  apply (subgoal_tac "leftFrom (rightP T) (rightP (rBtNeighb (tDagList D) T))") 
sorry
lemma nextNeighbour1: "trapezMapNeighbor D \<Longrightarrow> trapezList (tDagList D) \<Longrightarrow> tipInDag T D \<Longrightarrow>
  length (filter ((\<lambda>x. xCoord (rightP (rUpNeighb (tDagList D) T)) < x) \<circ> (xCoord \<circ> rightP))
          (tDagList D))
  < length (filter ((\<lambda>x. xCoord (rightP T) < x) \<circ> (xCoord \<circ> rightP)) (tDagList D))"
  apply (subgoal_tac "leftFrom (rightP T) (rightP (rBtNeighb (tDagList D) T))")
sorry

(*lemma tramMap_measure_size [measure_function]:"isTramMap D \<and> pointInDag D Q \<Longrightarrow>
  leftFrom (rightP T) ()"*)

(*gib eine trapezliste, die von PQ geschnitten werden zurück.*)
function followSeg :: "tDag \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  (*signedArea P Q (rightP T) \<noteq> 0 \<Longrightarrow> kann man beweisen, da PQ nicht durch rightP T durchgeht,
    und P Q nicht vollständig in T ist*)
  "followSeg D T P Q =
  (if (trapezMapNeighbor D \<and> trapezList (tDagList D) \<and> tipInDag T D \<and> pointInDag D Q \<and>
  leftFrom P Q) then (
    (if (xCoord (rightP T) < xCoord Q) then
      (if (leftTurn P Q (rightP T))
        then (T # followSeg D (rBtNeighb (tDagList D) T) P Q)
        else (T # followSeg D (rUpNeighb (tDagList D) T) P Q))
    else([T])))
   else ([]))"
by pat_completeness auto
termination followSeg
 apply (relation "measure (\<lambda> (D,T,P,Q). length (filter (\<lambda>x. xCoord(rightP T) < x)
   (map (xCoord o rightP)(tDagList D))))")
 (*beweise das das nächste Trapez rechts von dem linkem Trapez
  bzw. dass der Abstand zwischen rightP T und Q immer kleiner wird.
  Beweis mit Abstand für reale Zahlen garnicht möglich!
  Abstand kan beliebig klein werden und Q nicht erreichen
  Beweis sollte über die Anzahl der Elemente in der Liste sein, die noch als Nachbar in Frage kommen*)
by (auto simp add: nextNeighbour nextNeighbour1)

(*alle Trapeze aus followSeg sind aus D*)
lemma followSegmetInDag[simp]:"tipInDag T D \<Longrightarrow> A \<in> set (followSeg D T P Q) \<Longrightarrow>
  A \<in> set (tDagList D)"
  apply (induct D T P Q rule: followSeg.induct, simp)
  apply (simp add: conflictingLeftTurns3 set_ConsD tDagListComplete)
  apply (simp add: pointInDag_def set_ConsD tDagListComplete)
by (smt empty_iff followSeg.simps insert_iff list.set(1) list.set(2) notLeftTurn notRightTurn1)
lemma followSegmetInDag1: "A \<in> set (followSeg D (queryTrapezoidMap D P) P Q) \<Longrightarrow> tipInDag A D"
  using followSegmetInDag queryTrapezoidMapInDag tDagListComplete by blast


(*gib eine trapezliste, die von PQ geschnitten werden. Start-Trapez enthält P*)
definition intersectedTrapez :: "tDag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "leftFrom P Q \<Longrightarrow> intersectedTrapez D P Q \<equiv> followSeg D (queryTrapezoidMap D P) P Q"
lemma intersectedTrapezNotEmpty[simp]: "leftFrom p q \<Longrightarrow> rBoxTrapezS [p,q] R \<Longrightarrow>
  intersectedTrapez (Tip R) p q = [] \<Longrightarrow> False"
  apply (subgoal_tac "isTrapez R") defer apply (simp add: rBoxTrapezS_def)
  apply (subgoal_tac "trapezList [R]") defer apply (simp add: trapezList_def)
  apply (simp add: intersectedTrapez_def)
  apply (subgoal_tac "trapezMapNeighbor (Tip R) \<and> pointInDag (Tip R) q", simp)
  apply (subgoal_tac "xCoord (rightP R) \<ge> xCoord q", simp)
  apply (metis list.distinct(1))
  apply (auto) defer
using pointInDag_def pointInRBox by auto[1]

(*jedes Trapez von intersectedTrapez ist aus D*)
lemma intersectedTrapezInDag[simp]: "leftFrom P Q \<Longrightarrow> T \<in> set (intersectedTrapez D P Q) \<Longrightarrow>
  tipInDag T D"
  apply(simp add: intersectedTrapez_def)
by (smt empty_iff followSegmetInDag list.set(1) queryTrapezoidMapInDag rBtNeighbInDag1
  rUpNeighbInDag1 set_ConsD tDagListComplete)
(*enthält D nur eine rBox liefert intersectedTrapez die rBox zurück*)
lemma intersectedTrapezSimp[simp]: "leftFrom p q \<Longrightarrow> rBoxTrapezS [p,q] R \<Longrightarrow>
  intersectedTrapez (Tip R) p q = [R]"
  apply (subgoal_tac "isTrapez R") defer apply (simp add: rBoxTrapezS_def)
  apply (subgoal_tac "trapezList [R]") defer apply (simp add: trapezList_def)
  apply (simp only: intersectedTrapez_def)
  apply (subgoal_tac "queryTrapezoidMap (Tip R) p = R")
  apply (erule ssubst)
  apply (subgoal_tac "xCoord (rightP R) \<ge> xCoord q", auto)
  using pointInDag_def pointInRBox  apply auto[1]
using pointInRBox pointInTrapez_def by auto[1]
lemma intersectedTrapezSimp1[simp]: "isTrapez R \<Longrightarrow> leftFrom p q \<Longrightarrow> pointInDag (Tip R) q \<Longrightarrow>
  intersectedTrapez (Tip R) p q = [R]"
  apply (subgoal_tac "trapezList [R]") defer apply (simp add: trapezList_def)
  apply (simp only: intersectedTrapez_def)
  apply (subgoal_tac "queryTrapezoidMap (Tip R) p = R")
  apply (erule ssubst)
  apply (subgoal_tac "xCoord (rightP R) \<ge> xCoord q")
  apply (metis followSeg.simps isRBoxMapNeighbor rBtNeighbInDag
    rUpNeighbInDag tDagList.simps(1) tDagListComplete tipInDag.simps(1) trapezMapNeighbor_def)
  apply simp
using queryTrapezoidMap.simps(1) by blast

(*das erste Trapez enthält die linke Ecke*)
lemma intersectedHD[simp]: "trapezMapNeighbor D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow>
  trapezList (tDagList D) \<Longrightarrow> pointInDag D Q \<Longrightarrow> TM = intersectedTrapez D P Q \<Longrightarrow>
  hd(TM) = queryTrapezoidMap D P"
  by (simp add: intersectedTrapez_def)
(*das letzte Trapez enthält die letzte Ecke*)
lemma intersectedLast[intro]: "trapezMapNeighbor D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow>
  pointInDag D Q \<Longrightarrow> TM = intersectedTrapez D P Q \<Longrightarrow> trapezList (tDagList D) \<Longrightarrow>
  last(TM) = queryTrapezoidMap D Q \<or> leftP (queryTrapezoidMap D Q) = rightP (last TM)"
  apply (auto, simp only: intersectedTrapez_def)
oops

(*segment ist im Trapez dann liefert intersectedTrapez nur ein Trapez*)
lemma intersectOne: "trapezMapNeighbor D \<Longrightarrow> pointsInTramMap D \<Longrightarrow>
  trapezList (tDagList D)\<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  TM = intersectedTrapez D P Q \<Longrightarrow> queryTrapezoidMap D Q = queryTrapezoidMap D P \<Longrightarrow> length TM = 1"
  apply (auto, simp only: intersectedTrapez_def)
  apply (simp)
  apply (subgoal_tac "xCoord (rightP (queryTrapezoidMap D P)) \<ge> xCoord Q", simp)
using  pointsInTramMap_def by auto
lemma intersectOne1:"trapezMapNeighbor D \<Longrightarrow> pointsInTramMap D \<Longrightarrow> leftFrom P Q \<Longrightarrow>
  pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow> TM = intersectedTrapez D P Q \<Longrightarrow> trapezList (tDagList D) \<Longrightarrow>
  queryTrapezoidMap D P = T \<Longrightarrow> queryTrapezoidMap D Q = T\<Longrightarrow> TM = [T]"
  apply (auto, simp only: intersectedTrapez_def)
  apply (subgoal_tac "xCoord (rightP (queryTrapezoidMap D P)) \<ge> xCoord Q", simp)
using pointsInTramMap_def by auto

(*segment schneidet mehrere Trapeze, intersectedTrapez berechnet Folge von benachbarten Trapezen*)
lemma intersectedTrapezComp: "trapezMapNeighbor D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow>
  pointInDag D Q \<Longrightarrow> TM = intersectedTrapez D P Q \<Longrightarrow> trapezList (tDagList D) \<Longrightarrow>
  (\<forall> i < length TM - 1. neighborAlongSeg (TM!i) (TM!Suc i) P Q)"
  apply (induct TM, auto)
oops
(*Q kann nur sich nur im letzten Trapez befinden *)
lemma intersectedTrapezPos: "trapezMapNeighbor D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow>
  pointInDag D Q \<Longrightarrow> trapezList (tDagList D) \<Longrightarrow>
  \<not> (\<exists>i<length (intersectedTrapez D P Q) - 1. i \<noteq> 0 \<and> rightP (intersectedTrapez D P Q ! i) = Q)"
oops
(*P kann nur sich nur im ersten Trapez befinden *)
lemma intersectedTrapezPos1: "trapezMapNeighbor D \<Longrightarrow> leftFrom P Q \<Longrightarrow> pointInDag D P \<Longrightarrow>
  pointInDag D Q \<Longrightarrow> trapezList (tDagList D) \<Longrightarrow>
  \<not>(\<exists> i. i < length (intersectedTrapez D P Q) \<and> i \<noteq> 0 \<and> leftP ((intersectedTrapez D P Q)!i) = P)"
oops




(*#######Füge neue Segmente in die Trapezoidal-Map ein#########*)

(*ersetzt alle übergebenen Trapeze im tDag durch neue Trapeze, die mit PQ erstellt wurden
Input : suchBaum D, 2 mal Liste mit Trapezen die ersetzt werden sollen,Segment PQ
Output: neues Dag, nachdem alle Trapeze ersetzt wurden*)
fun replaceDag :: "tDag \<Rightarrow> trapez list \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "replaceDag D [] TM P Q = D"
  | "replaceDag D (T#Ts) TM P Q = replaceDag (replaceTip T (newDag D T TM P Q ) D) Ts TM P Q"
(*Inhalt von tDag nach replaceDag*)
lemma replaceDagXDagList[intro]: "a \<in> set (xDagList D) \<longrightarrow> 
  a \<in> set (xDagList (replaceDag D TM TN P Q))"
  by (induct D TM TN P Q rule: replaceDag.induct, auto)
lemma replaceXDagListElem[intro]: "a \<in> set (xDagList (replaceDag D TM TN P Q)) \<longrightarrow>
  a \<in> set (xDagList D) \<or> a = P \<or> a = Q"
  apply (induct D TM TN P Q rule: replaceDag.induct, auto)
by (metis empty_iff insert_iff list.set(1) list.set(2) replaceTipXDagList1 xDagListNewDag)
lemma replaceYDagListElem[intro]:"a \<in> set (yDagList (replaceDag D TM TN P Q)) \<longrightarrow>
  a \<in> set (yDagList D) \<or> a = (P,Q)"
  apply (induct rule: replaceDag.induct)
  apply (auto)
  apply (cut_tac a=a and oT=T and nT="newDag D T TM P Q" and D=D in replaceTipYDagList1, assumption)
by(auto)


lemma replaceRBoxNotSame[simp]:"leftFrom p q \<Longrightarrow> rBoxTrapezS [p,q] R \<Longrightarrow>
  replaceDag (Tip R) (intersectedTrapez (Tip R) p q) (intersectedTrapez (Tip R) p q) p q \<noteq> Tip R"
by (simp)

(******add Segment to trapezoidal-map*)
(*erneure tDag nach dem hinzufügen eines segments*)
definition addSegmentToTrapMap :: "tDag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "leftFrom P Q \<Longrightarrow> addSegmentToTrapMap D P Q \<equiv>
    replaceDag D(intersectedTrapez D P Q)(intersectedTrapez D P Q) P Q"
lemma addSegmentToRBoxNotSame [simp]:"leftFrom p q \<Longrightarrow> rBoxTrapezS [p,q] R \<Longrightarrow>
  addSegmentToTrapMap (Tip R) p q \<noteq> Tip R"
  apply (simp add: addSegmentToTrapMap_def)
done


(*****Add Polygon to trapezoidal-map*)
(*Input: List of line segments(one Polygon) forming a planar subdivision.
Output:  A trapezoid map M in associated search structure tDag.*)
fun addSegmentsToTrapMap :: "tDag \<Rightarrow> point2d list \<Rightarrow> tDag" where
  "addSegmentsToTrapMap D [] = D"
  | "addSegmentsToTrapMap D [p] = D"
  | "addSegmentsToTrapMap D (p#q#xs) = addSegmentsToTrapMap
    (addSegmentToTrapMap D (leftPSegment p q) (rightPSegment p q)) (q#xs)"

fun addPolygonsToTrapMap :: "tDag \<Rightarrow> (point2d list) list \<Rightarrow> tDag" where
   "addPolygonsToTrapMap D [] = D"
  | "addPolygonsToTrapMap D (x#xs) = addPolygonsToTrapMap (addSegmentsToTrapMap D x) xs"




(*alte Definition*)

end