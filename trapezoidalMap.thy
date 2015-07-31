theory trapezoidalMap
imports tDag
begin

(*zwei Trapeze sind benachbart entland der Strecke PQ, wenn :
  - die linke Ecke eines Trapezes gleich der rechten Ecke des anderen Trapezes
  - topT gleich sind, falls PQ über rightPT bzw. bottomT gleich sind, falls PQ unter rightP.*)
definition neighbTrapez:: "tDag \<Rightarrow> trapez \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "tipInDag T D \<Longrightarrow> tipInDag Ts D \<Longrightarrow> neighbTrapez D T Ts P Q \<equiv> rightP T = leftP Ts \<and>
  ((rightTurn P Q (rightP T) \<and> topT T = topT Ts) \<or> (leftTurn P Q (rightP T) \<and> bottomT T = bottomT Ts))"
lemma neighbTrapezSame [dest] : "tipInDag T D \<Longrightarrow> neighbTrapez D T T P Q \<Longrightarrow> False"
  by (auto simp add: neighbTrapez_def,(metis leftFromPoint_def less_irrefl trapezNeighbour2)+)

(*gib den nächsten Nachbarn von einem Trapez folgend der Strecke PQ  aus der Trapez-Liste
Input: tDag, tDagList geordnet nach der x-Coordinate von leftP, Strecke PQ
Output: nächster trapez-Nachbar, wenn man PQ folgt*)
(*es muss ein Nachbar geben! kein Nachbar wird ausgelassen!*)
fun nextTrapez :: "tDag \<Rightarrow> trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez" where
  "nextTrapez D (Ts#Tm) T P Q = (if(neighbTrapez D T Ts P Q) then(Ts) else(nextTrapez D Tm T P Q))"

(*gehe solange bis zum nächsten Nachbarn bis gesuchte Ecke gefunden ist
Input: funktion die linke/rechte Ecke vom Trapez gibt, Liste mit Trapezen durch die PQ geht,
  Entscheidung Trapez-Ecke über/unter segment PQ liegt, Strecke PQ
Output: nächste linke/rechte Ecke die über/unter dem Segment P/Q liegt*)
fun nextCorner :: "(trapez \<Rightarrow> point2d) \<Rightarrow> trapez list \<Rightarrow> (point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool) \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "nextCorner f [TM] _  _ _ = f TM"
  |" nextCorner f (TM#TS) g P Q = (if (g (f TM) P Q) then (f TM) else (nextCorner f TS g P Q))"

(*gehe solange von T zum nächsten linken Nachbarn, bis leftP des Trapez über PQ liegt*)
definition topLeftCorner:: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "topLeftCorner TM T P Q = nextCorner leftP (dropWhile (trapezNotEq T) (rev TM)) leftTurn P Q"
(*gehe solange von T zum nächsten rechten Nachbarn, bis rightP des Trapez über PQ liegt*)
definition topRightCorner :: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "topRightCorner TM T P Q = nextCorner rightP (dropWhile (trapezNotEq T) TM) leftTurn P Q"
(*gehe solange von T zum nächsten linken Nachbarn, bis leftP des Trapez unter PQ liegt*)
definition bottomLeftCorner :: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "bottomLeftCorner TM T P Q = nextCorner leftP (dropWhile (trapezNotEq T) (rev TM)) rightTurn P Q"
(*gehe solange von T zum nächsten rechten Nachbarn, bis rightP des Trapez unter PQ liegt*)
definition bottomRightCorner :: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "bottomRightCorner TM T P Q = nextCorner rightP (dropWhile (trapezNotEq T) TM) rightTurn P Q"

(*jedes Trapez dessen rightP \<le> x ist ist im Tl von Tl x Tr*)
fun trapezoidalMapX :: "tDag \<Rightarrow> real \<Rightarrow> bool" where
  "trapezoidalMapX (Tip T) x = (xCoord(rightP T) \<le> x)"
  | "trapezoidalMapX (Node lf (xNode n) rt) x = trapezoidalMapX lf x"
fun trapezoidalMapX1 :: "tDag \<Rightarrow> real \<Rightarrow> bool" where
  "trapezoidalMapX1 (Tip T) x = (xCoord(leftP T) \<ge> x)"
  | "trapezoidalMapX1 (Node lf (xNode n) rt) x = trapezoidalMapX1 lf x"
fun trapezoidalMapY :: "tDag \<Rightarrow> (point2d*point2d) \<Rightarrow> bool" where
  "trapezoidalMapY (Tip T) y = (signedArea (fst y) (snd y) (rightP T) \<ge> 0)"
  | "trapezoidalMapY (Node lf (yNode n) rt) y = trapezoidalMapY lf y"
fun trapezoidalMapY1 :: "tDag \<Rightarrow> (point2d*point2d) \<Rightarrow> bool" where
  "trapezoidalMapY1 (Tip T) y = (signedArea (fst y) (snd y) (rightP T) \<le> 0)"
  | "trapezoidalMapY1 (Node lf (yNode n) rt) y = trapezoidalMapY1 lf y"
(*jedes Trapez in tDag ist so aufgebaut, dass für alle Trapeze in lf im Baum (Node lf k rt) gilt:
  -rechteEcke von Trapez ist links von k
  -rechteEcke ist über der Kante k *)
fun trapezoidalMap1 :: "tDag \<Rightarrow> bool" where
  "trapezoidalMap1 (Tip T)  = True"
  | "trapezoidalMap1 (Node lf (xNode x) rt) = (trapezoidalMapX lf (xCoord x) \<and> trapezoidalMapX1 rt (xCoord x))"
  | "trapezoidalMap1 (Node lf (yNode y) rt) = (trapezoidalMapY lf y \<and> trapezoidalMapY1 rt y)"


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
(*welche Annahmen müssen in tDag stecken damit das stimmt? das tDag mit simpTrapezoidalMap gebaut wurde?*)
lemma "queryTrapezoidMap Tl P = queryTrapezoidMap (Node Tl x Tr) P"
  apply (case_tac x, simp, safe)
  apply (case_tac "(Tl, P)" rule: queryTrapezoidMap.cases)
  apply (auto)
oops
lemma queryTrapezoidMapComplete : "tipInDag T D \<longleftrightarrow> (\<exists> P. T = (queryTrapezoidMap D P))"
  apply (induction D, auto)
  apply (rule_tac x=Pb in exI)
sorry
lemma queryTrapezoidMapInDag: "tipInDag (queryTrapezoidMap D P) D" by (auto simp add: queryTrapezoidMapComplete)


(*Einfacher Fall: allgemeinFall. weder P noch Q sind in T drin, auch nicht an den Ecken*)
definition newDagSimpA :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagSimpA  T P Q =
   Node (Tip (Abs_trapez (topT T,(P,Q),P,Q)))
    (yNode (P,Q))
   (Tip (Abs_trapez ((P,Q),bottomT T,P,Q)))"

(*Einfacher Fall: füge Q hinzu, P bereits betrachtet*)
definition newDagSimpQ :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagSimpQ T P Q =
    Node (newDagSimpA T P Q)
      (xNode Q)
    (Tip (Abs_trapez(topT T,bottomT T,Q,rightP T)))"

(*Einfacher Fall: wenn P und Q in T liegen*)
definition newDagSimp :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagSimp  T P Q = (
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

(*ersetze mittlere Trapeze, d.h. P liegt in T0, Q liegt in Tn und Trapez Ti(0<i<n) soll ersetzt werden*)
definition newDagM :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
   "newDagM  T TM P Q =
   Node (Tip (Abs_trapez(topT T,(P,Q),(topLeftCorner TM T P Q), (topRightCorner TM T P Q))))
      (yNode (P,Q))
    (Tip (Abs_trapez((P,Q), bottomT T, (bottomLeftCorner TM T P Q), (bottomRightCorner TM T P Q))))"

(*gegebenes Trapez wird durch 2 neue Trapeze ersetzt; geteilt durch die Strecke PQ*)
definition newDagFirstY :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagFirstY T TM P Q =
  Node (Tip (Abs_trapez(topT T, (P,Q), P, (topRightCorner TM T P Q))))
    (yNode (P,Q))
   (Tip (Abs_trapez((P,Q), bottomT T, P, (bottomRightCorner TM T P Q))))"

(*Das erste Trapez soll ersetzt werden, zu überprüfen ist ob Ecke im Trapez ist oder auf der Kante*)
definition newDagFirst :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagFirst T TM P Q = (
  if (leftP T = P) then(newDagFirstY T TM P Q)
  else (Node (Tip (Abs_trapez(topT T, bottomT T, leftP T, P)))
    (xNode P)
  (newDagFirstY T TM P Q) ))"

(*gegebenes Trapez wird durch 2 neue Trapeze ersetzt; geteilt durch die Strecke PQ*)
definition newDagLastY :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
   "newDagLastY T TM P Q = Node (Tip (Abs_trapez(topT T, (P,Q), topLeftCorner TM T P Q, Q)))
    (yNode (P,Q))
   (Tip (Abs_trapez((P,Q),bottomT T, bottomLeftCorner TM T P Q, Q)))"

(*Das letzte Trapez soll ersetzt werden, zu überprüfen ist ob Ecke im Trapez ist oder auf der Kante*)
definition newDagLast :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagLast T TM P Q = (
  if (rightP T = Q) then(newDagLastY T TM P Q)
  else (Node (newDagLastY T TM P Q)
   (xNode Q)
  (Tip (Abs_trapez(topT T,bottomT T, Q, rightP T)))
  ))"

(*Algorithm newDag(tDag,trapez, trapez list, segment)*)
(*Input: SuchBaum D, Trapez T das ersetz werden soll, Trapezliste TM mit Trapezen die Strecke PQ kreuzt, Strecke PQ(linksgeordnet)
Output: tDag welches Trapez T ersetzen soll*)
definition newDag :: "tDag \<Rightarrow> trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
"newDag D T TM P Q = (if (length TM = 1) then (newDagSimp T P Q)
    else (if (queryTrapezoidMap D P = T) then (newDagFirst T TM P Q)
      else (if (queryTrapezoidMap D Q = T \<or> rightP T = Q) then (newDagLast T TM P Q)
        else (newDagM T TM P Q)
      )
    ))"


(*gib eine Liste mit trapezen zurück die das Segment PQ schneiden. Reihenfolge von links nach rechts
Input: suchBaum D, trapez list ist nach x-Coord von leftP sortiert, Start Trapez(in dem sich P befindet), Segment PQ
Output: liste mit trapezen*)
(*man verpasst kein Nachbar! weil immer der nächste Nachbar gefunden wird, bevor man zu den zweitem kommen kann!*)
fun followSegment :: "tDag \<Rightarrow> trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where 
  "followSegment _ [] _ _ _ = []"
  | "followSegment D (Ts#TM) T P Q = (if (xCoord Q \<ge> xCoord (rightP T) \<and> neighbTrapez D T Ts P Q)
    then (Ts # (followSegment D TM Ts P Q)) else (followSegment D TM T P Q))"
lemma "length (tDagList D) > 1\<Longrightarrow>
  Ts = nextTrapez D (tDagList D) T P Q \<Longrightarrow> leftFromPoint (rightP T) (rightP Ts)"
  apply (cases "tDagList D", simp)
  apply (auto simp add: neighbTrapez_def)
  
  sorry
(*es gibt ein T in D sodass rightP T > Q*)

(*gib eine trapezliste, die on PQ geschnitten werden.*)
(*Nochmal anschauen! bzw. muss das erste Trapez(indem PQ steckt) nicht noch angefügt werden*)
definition intersectedTrapez :: "tDag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "intersectedTrapez D P Q = (queryTrapezoidMap D P) #
  (followSegment D (sortedTrapez (tDagList D)) (queryTrapezoidMap D P) P Q)"


(*ersetzt alle übergebenen Trapeze im tDag durch neue Trapeze, die mit PQ erstellt wurden
Input : suchBaum D, 2 mal Liste mit Trapezen die ersetzt werden sollen,Segment PQ
Output: neues Dag, nachdem alle Trapeze ersetzt wurden*)
fun replaceDag :: "tDag \<Rightarrow> trapez list \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "replaceDag D [] _ _ _ = D"
  | "replaceDag D (T#Ts) TM P Q = replaceDag (replaceTip T (newDag D T TM P Q ) D) Ts TM P Q"







(*erneure tDag nach dem hinzufügen eines segments*)
definition addSegmentToTrapezoidalMap :: "tDag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "leftFromPoint P Q \<Longrightarrow> addSegmentToTrapezoidalMap D P Q \<equiv>
    replaceDag D (intersectedTrapez D P Q) (intersectedTrapez D P Q) P Q"


(*wenn a in einem Trapez, dann ist a in einem der neuem Trapeze*)
(*füge Segment in rBox ein*)
lemma addSegmentToRBox: "leftFromPoint P Q \<Longrightarrow> pointList [P,Q,a] \<Longrightarrow> rBoxTrapezS [P,Q,a] R \<Longrightarrow>
  D =(addSegmentToTrapezoidalMap (Tip R) P Q) \<Longrightarrow>
  \<exists> i < length (tDagList D). pointInTrapez ((tDagList D)!i) a"
  apply (simp add: addSegmentToTrapezoidalMap_def)
  apply (simp add: intersectedTrapez_def sortedTrapez_def)
  apply (subgoal_tac "\<not>neighbTrapez (Tip R) R R P Q")
  apply (simp, thin_tac "\<not>neighbTrapez (Tip R) R R P Q")
  apply (simp add: newDag_def)
  apply (simp add: newDagSimp_def)
  apply (subgoal_tac "leftP R \<noteq> P \<and> rightP R \<noteq> Q", simp add: newDagSimpQ_def newDagSimpA_def)
  apply (thin_tac "leftP R \<noteq> P \<and> rightP R \<noteq> Q")
  apply (simp add: rBoxTrapezS_def pointInRBox_def, erule_tac x=2 in allE, simp)
  apply (thin_tac "pointList [P, Q, a]")
  apply (case_tac "xCoord a < xCoord P")
    apply (rule_tac x=0 in exI, simp add: pointInTrapez_def)
  apply (metis leftFromPoint_def leftP leftPRigthFromRightP less_not_sym rightP)+
done
lemma addSegmentToRBox1: "leftFromPoint P Q \<Longrightarrow> pointList [P,Q,a] \<Longrightarrow> rBoxTrapezS [P,Q,a] R \<Longrightarrow>
  D =(addSegmentToTrapezoidalMap (Tip R) P Q) \<Longrightarrow>
  (\<exists> i < length (tDagList D). pointInTrapez ((tDagList D)!i) a \<and> ((tDagList D)!i = queryTrapezoidMap D a))"
  apply (simp add: addSegmentToTrapezoidalMap_def)
  apply (simp add: intersectedTrapez_def sortedTrapez_def)
  apply (subgoal_tac "\<not>neighbTrapez (Tip R) R R P Q")
  apply (simp, thin_tac "\<not>neighbTrapez (Tip R) R R P Q")
  apply (simp add: newDag_def)
  apply (simp add: newDagSimp_def)
  apply (subgoal_tac "leftP R \<noteq> P \<and> rightP R \<noteq> Q", simp add: newDagSimpQ_def newDagSimpA_def)
  apply (thin_tac "leftP R \<noteq> P \<and> rightP R \<noteq> Q")
  apply (simp add: rBoxTrapezS_def pointInRBox_def, erule_tac x=2 in allE, simp)
  apply (thin_tac "pointList [P, Q, a]")
  apply (case_tac "xCoord a < xCoord P", auto)
  apply (metis leftFromPoint_def leftP leftPRigthFromRightP less_not_sym rightP)+
done
(*füge Segment in tDag ein, wenn tDag \<noteq> rBox*)
lemma addSegmentToRBox: "leftFromPoint P Q \<Longrightarrow> pointList [P,Q,a] \<Longrightarrow> rBoxTrapezS [P,Q,a] R \<Longrightarrow>
  D =(addSegmentToTrapezoidalMap dag P Q) \<Longrightarrow> (*wie macht man eine Aussage über dag*)
  \<exists> i < length (tDagList D). pointInTrapez ((tDagList D)!i) a"
oops


(*zeige das keine der Seiten von den neuen trapezodialMaps das polygon innerhalb von rBox schneidet*)
(*untere und obere Strecken von trapezen, sind segmente von den polygonen*)

(*linke und rechte Strecke von trapezen schneiden die Polygone nicht(echt). *)






(*Input: List of line segments(one Polygon) forming a planar subdivision.
Output:  A trapezoid map M in associated search structure tDag.*)
fun addPolygonToTrapezoidalMap :: "tDag \<Rightarrow> point2d list \<Rightarrow> tDag" where
  "addPolygonToTrapezoidalMap D [] = D"
  | "addPolygonToTrapezoidalMap D [q] = D"
  | "addPolygonToTrapezoidalMap D (p#q#xs) =
  addPolygonToTrapezoidalMap (addSegmentToTrapezoidalMap D (leftPSegment p q) (rightPSegment p q)) (q#xs)"



(*Beweise erstmal mit nur einem Polygon*)

(*Input: rBox, tDag(start with rBox) and a polygon forming a planar subdivision.
Output:  A trapezoid map M in associated search structure tDag.*)
definition simpTrapezoidalMap :: "point2d list \<Rightarrow> point2d list \<Rightarrow> tDag" where
  "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> uniqueXCoord L \<Longrightarrow> rBoxS R P \<Longrightarrow>
  simpTrapezoidalMap R P \<equiv> addPolygonToTrapezoidalMap (Tip (rBoxTrapez R)) P"

(*zeige das keine der segmente von trapezodialMap das polygon innerhalb von rBox schneidet*)
(*untere und obere Strecken von trapezen, sind segmente von den polygonen*)
lemma "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> uniqueXCoord L \<Longrightarrow> rBoxS R L \<Longrightarrow>
  TL = tDagList (simpTrapezoidalMap R P) \<Longrightarrow> i < length TL \<longrightarrow>
    segInPointList P (bottomT(TL!i)) \<and> segInPointList P (topT(TL!i))"
  apply (auto simp add: segInPointLists_def)
oops
(*linke und rechte Strecke von trapezen schneiden die Polygone nicht(echt).
dafür müsste man jedoch leftT und rightT ausrechnen. einfacher wäre es evtl., wenn man impliziet zeigt
dass leftT und rightT vertikale(müssen die das sein?) sind und von topT und bottomT begrenzt werden,
d.h. andere segmente nicht schneiden*)
lemma "pointLists L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> uniqueXCoord L \<Longrightarrow> rBoxS R L \<Longrightarrow>
  TL = tDagList (simpTrapezoidalMap R P)
  \<Longrightarrow> i < length TL \<Longrightarrow> j < length TL \<Longrightarrow> \<not>polygonCrossing (PL!j) (TL!i)" (*lineCyclePathInters*)  
oops




(*entferne die übrigen strecken die noch innerhalb der Polygone sind*)

(*zeige das keine der Strecken von trapezoidalMap im Polygon sind*)

(*zeige das die trapezoidalMap jetzt eine Einteilung der Freien-Räume innerhalb der rBox ist*)

(*roadMap. Eingabe TrapezodiodamMap T*)

(*beweise das Strecken zwischen RaodMap immer Kollisionsfrei*)



(*alte Definition*)
(*beweise das das nächste Trapez rechts von dem linkem Trapez*)
lemma "leftFromPoint P Q \<Longrightarrow> Tl = queryTrapezoidMap D P \<Longrightarrow> Tl \<noteq> Tr \<Longrightarrow> Tr = queryTrapezoidMap D R \<Longrightarrow> 
  leftFromPoint (leftP Tl) (leftP (nextTrapez D (tDagList D) Tl P Q))"
  apply (subgoal_tac "tDagList D \<noteq> []")
  apply (case_tac "(D, (tDagList D), Tl, P, Q)" rule: nextTrapez.cases)
  apply (auto)
oops
(*The termination argument for followS is based on the fact that the difference
between "xCoord (rightP T)" and  "xCoord Q"  gets smaller in every step*) 
function followS :: "tDag \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "followS D T P Q = (if(leftFromPoint (rightP T) Q)
  then(followS D (nextTrapez D (tDagList D) T P Q) P Q)
  else ([]))"
by pat_completeness auto
termination followS (*beweise das das nächste Trapez rechts von dem linkem Trapez
  bzw. dass der Abstand zwischen rightP T und Q immer kleiner wird*)
(*dafür müssen aber entweder in tDag noch annahmen stecken oder es muss eine condition für followS geben*)
(*functions with conditional patterns are not supported by the code generator.*)
sorry
(*lemma "queryTrapezoidMap D p = queryTrapezoidMap D q \<Longrightarrow> followSegment D p q = tDagList(D)"
  apply (simp only: followSegment_def)
  apply (cases D)
oops*)

(*
(*Input: tDag(start with rBox) and List of polygons forming a planar subdivision.
Output:  A trapezoid map M in associated search structure tDag.*)
fun buildTrapezoidalMap :: "tDag \<Rightarrow> (point2d list) list \<Rightarrow> tDag" where
  "buildTrapezoidalMap D [] = D"
  |"buildTrapezoidalMap D (P#Pl) = buildTrapezoidalMap (polygonExtendTrapezoidalMap D P) Pl"*)

(*
lemma "T = queryTrapezoidMap D q \<Longrightarrow> followSegment D T p q = [T]"
  apply (simp)
  apply (safe)
oops*)
end
