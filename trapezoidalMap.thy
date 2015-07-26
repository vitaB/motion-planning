theory trapezoidalMap
imports tDag
begin

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

(*Algorithm QueryTrapezoidMap(dag,point2d)
Input: T is the trapezoid map search structure, n is a node in the search structure and p is a query point.
Output:  A pointer to the node in D for the trapezoid containing the point p.*)
fun queryTrapezoidMap :: "dag \<Rightarrow> point2d \<Rightarrow> trapez" where
  "queryTrapezoidMap (Tip T) _ =  T"
  |"queryTrapezoidMap (Node lf (xNode n) rt) p = 
   (if (xCoord p < xCoord n) then (queryTrapezoidMap lf p) else (queryTrapezoidMap rt p))"
  |"queryTrapezoidMap (Node lf (yNode x) rt) p =
  (*lf ist über dem segment x, rt ist unter dem segment*)
   (if (leftTurn (fst x) (snd x) p) then (queryTrapezoidMap lf p) else (queryTrapezoidMap rt p))"


(*Einfacher Fall: allgemeinFall. weder P noch Q sind in T drin, auch nicht an den Ecken*)
definition newDagSimpA :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "newDagSimpA  T P Q =
   Node (Tip (Abs_trapez (topT T,(P,Q),P,Q)))
    (yNode (P,Q))
   (Tip (Abs_trapez ((P,Q),bottomT T,P,Q)))"

(*Einfacher Fall: füge Q hinzu, P bereits betrachtet*)
definition newDagSimpQ :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "newDagSimpQ T P Q =
    Node (newDagSimpA T P Q)
      (xNode Q)
    (Tip (Abs_trapez(topT T,bottomT T,Q,rightP T)))"

(*Einfacher Fall: wenn P und Q in T liegen*)
definition newDagSimp :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
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
definition newDagM :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
   "newDagM  T TM P Q =
   Node (Tip (Abs_trapez(topT T,(P,Q),(topLeftCorner TM T P Q), (topRightCorner TM T P Q))))
      (yNode (P,Q))
    (Tip (Abs_trapez((P,Q), bottomT T, (bottomLeftCorner TM T P Q), (bottomRightCorner TM T P Q))))"

(*gegebenes Trapez wird durch 2 neue Trapeze ersetzt; geteilt durch die Strecke PQ*)
definition newDagFirstY :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "newDagFirstY T TM P Q =
  Node (Tip (Abs_trapez(topT T, (P,Q), P, (topRightCorner TM T P Q))))
    (yNode (P,Q))
   (Tip (Abs_trapez((P,Q), bottomT T, P, (bottomRightCorner TM T P Q))))"

(*Das erste Trapez soll ersetzt werden, zu überprüfen ist ob Ecke im Trapez ist oder auf der Kante*)
definition newDagFirst :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "newDagFirst T TM P Q = (
  if (leftP T = P) then(newDagFirstY T TM P Q)
  else (Node (Tip (Abs_trapez(topT T, bottomT T, leftP T, P)))
    (xNode P)
  (newDagFirstY T TM P Q) ))"

(*gegebenes Trapez wird durch 2 neue Trapeze ersetzt; geteilt durch die Strecke PQ*)
definition newDagLastY :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
   "newDagLastY T TM P Q = Node (Tip (Abs_trapez(topT T, (P,Q), topLeftCorner TM T P Q, Q)))
    (yNode (P,Q))
   (Tip (Abs_trapez((P,Q),bottomT T, bottomLeftCorner TM T P Q, Q)))"

(*Das letzte Trapez soll ersetzt werden, zu überprüfen ist ob Ecke im Trapez ist oder auf der Kante*)
definition newDagLast :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "newDagLast T TM P Q = (
  if (rightP T = Q) then(newDagLastY T TM P Q)
  else (Node (newDagLastY T TM P Q)
   (xNode Q)
  (Tip (Abs_trapez(topT T,bottomT T, Q, rightP T)))
  ))"

(*Algorithm newDag(dag,trapez, trapez list, segment)*)
(*Input: SuchBaum D, Trapez T das ersetz werden soll, Trapezliste TM mit Trapezen die Strecke PQ kreuzt, Strecke PQ(linksgeordnet)
Output: dag welches Trapez T ersetzen soll*)
definition newDag :: "dag \<Rightarrow> trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
"newDag D T TM P Q = (if (length TM = 1) then (newDagSimp T P Q)
    else (if (queryTrapezoidMap D P = T) then (newDagFirst T TM P Q)
      else (if (queryTrapezoidMap D Q = T \<or> rightP T = Q) then (newDagLast T TM P Q)
        else (newDagM T TM P Q)
      )
    ))"


(*gib eine Liste mit trapezen zurück die das Segment PQ schneiden. Reihenfolge von links nach rechts
Input: suchBaum D, trapez list ist nach x-Coord von leftP sortiert und ist im Bereich P und Q, Start Trapez(in dem sich P befindet), Segment PQ
Output: liste mit trapezen*)
(*man verpasst kein Nachbar! weil immer der nächste Nachbar gefunden wird, bevor man zu den zweitem kommen kann!*)
fun followSegment :: "dag \<Rightarrow> trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where 
  "followSegment _ [] _ _ _ = []"
  | "followSegment D (Ts#TM) T P Q = (if (neighbTrapez D T Ts P Q)
    then (Ts # (followSegment D TM Ts P Q)) else (followSegment D TM T P Q))"
lemma "length (dagList D) > 1\<Longrightarrow>
  Ts = nextTrapez D (dagList D) T P Q \<Longrightarrow> leftFromPoint (rightP T) (rightP Ts)"
  apply (cases "dagList D", simp)
  apply (auto simp add: neighbTrapez_def)
  
  sorry
(*es gibt ein T in D sodass rightP T > Q*)

(*gib eine trapezliste, die on PQ geschnitten werden.*)
(*Nochmal anschauen! bzw. muss das erste Trapez(indem PQ steckt) nicht noch angefügt werden*)
definition intersectedTrapez :: "dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "intersectedTrapez D P Q = (queryTrapezoidMap D P) #
  (followSegment D (sortedIntersectTrapez (dagList D) P Q) (queryTrapezoidMap D P) P Q)"


(*ersetzt alle übergebenen Trapeze im dag durch neue Trapeze, die mit PQ erstellt wurden
Input : suchBaum D, 2 mal Liste mit Trapezen die ersetzt werden sollen,Segment PQ
Output: neues Dag, nachdem alle Trapeze ersetzt wurden*)
fun replaceDag :: "dag \<Rightarrow> trapez list \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "replaceDag D [] _ _ _ = D"
  | "replaceDag D (T#Ts) TM P Q = replaceDag (replaceTip T (newDag D T TM P Q ) D) Ts TM P Q"


(*erneure dag nach dem hinzufügen eines segments*)
definition addSegmentToTrapezoidalMap :: "dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "addSegmentToTrapezoidalMap D P Q \<equiv> replaceDag D (intersectedTrapez D P Q) (intersectedTrapez D P Q) P Q"
(*wenn a in einem Trapez, dann ist a in einem der neuem Trapeze*)
lemma "pointInTrapez T P \<Longrightarrow> pointInTrapez T Q \<Longrightarrow> pointInTrapez T a \<Longrightarrow> 
  D=dagList (addSegmentToTrapezoidalMap (Tip T) P Q) \<Longrightarrow> \<exists> i < length D. pointInTrapez (D!i) a"
  apply (simp add: addSegmentToTrapezoidalMap_def followSegment_def) (*del:followSegment.simps*)
oops
(*zeige das jedes neue Trapez ein convexes Polygon ist*)
lemma "segment P Q \<Longrightarrow> uniqueXCoord (P#Q#S) \<Longrightarrow> pointList R \<Longrightarrow> rBoxS R (P#Q#S) \<Longrightarrow>
 DS = addSegmentToTrapezoidalMap (Tip (rBoxTrapez R)) P Q \<Longrightarrow> \<forall> a \<in> set (dagList(DS)). trapezIsCPolygon a"
 apply (simp add: addSegmentToTrapezoidalMap_def)
oops

(*zeige das keine der Seiten von den neuen trapezodialMaps das polygon innerhalb von rBox schneidet*)
(*untere und obere Strecken von trapezen, sind segmente von den polygonen*)

(*linke und rechte Strecke von trapezen schneiden die Polygone nicht(echt). *)






(*Input: List of line segments(one Polygon) forming a planar subdivision.
Output:  A trapezoid map M in associated search structure dag.*)
fun addPolygonToTrapezoidalMap :: "dag \<Rightarrow> point2d list \<Rightarrow> dag" where
  "addPolygonToTrapezoidalMap D [] = D"
  | "addPolygonToTrapezoidalMap D [q] = D"
  | "addPolygonToTrapezoidalMap D (p#q#xs) =
  addPolygonToTrapezoidalMap (addSegmentToTrapezoidalMap D (leftPSegment p q) (rightPSegment p q)) (q#xs)"

(*Input: rBox, dag(start with rBox) and a polygon forming a planar subdivision.
Output:  A trapezoid map M in associated search structure dag.*)
definition simpTrapezoidalMap :: "point2d list \<Rightarrow> point2d list \<Rightarrow> dag" where
  "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> uniqueXCoord L \<Longrightarrow> rBoxS R P \<Longrightarrow>
  simpTrapezoidalMap R P \<equiv> addPolygonToTrapezoidalMap (Tip (rBoxTrapez R)) P"


(*Beweise erstmal mit nur einem Polygon*)
lemma "pointLists [P] \<Longrightarrow> polygonList [P] \<Longrightarrow> uniqueXCoord P \<Longrightarrow> TL = dagList (trapezoidalMap [P])
  \<Longrightarrow> i < length TL \<longrightarrow> trapezCollinearFree (TL!i)"
  apply (simp add: trapezoidalMap_def, safe)
  apply (rule_tac x="((Tip (rBoxTrapez [P])), P)" in polygonExtendTrapezoidalMap.cases, blast)
  apply (simp)
  apply (simp)
  apply (case_tac "(leftPSegment p q) = p")
  apply (subgoal_tac " (rightPSegment p q) = q")
  apply (simp)
  apply (simp add: segmentExtendTrapezoidalMap_def)
oops
(*trapeze sind keine collinearListen*)
lemma "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow> TL = dagList (trapezoidalMap PL)
  \<Longrightarrow> i < length TL \<longrightarrow> trapezCollinearFree(TL!i)"
  apply (simp add: collinearList_def)
  apply (safe)
  apply (induction i, simp)
  apply (cases PL)
  apply (simp add: pointLists_def)
  apply (simp add: trapezoidalMap_def rBoxTrapez_def)
  apply (case_tac "aa", blast)
  apply (simp add: rBox_def)

oops
(*zeige das jedes Trapez ein convexes Polygon ist*)
lemma "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow> TL = dagList (trapezoidalMap PL)
  \<Longrightarrow> i < length TL \<longrightarrow> cPolygon (cyclePath (trapezToPointList (TL!i)))"
  apply (simp add: cPolygon_def)
oops

(*zeige das keine der segmente von trapezodialMap das polygon innerhalb von rBox schneidet*)
(*untere und obere Strecken von trapezen, sind segmente von den polygonen*)
lemma "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow> TL = dagList (trapezoidalMap PL)
  \<Longrightarrow> i < length TL \<longrightarrow> segInPointLists PL (bottomT(TL!i)) \<and> segInPointLists PL (topT(TL!i))"
  apply (auto simp add: segInPointLists_def)
oops
(*linke und rechte Strecke von trapezen schneiden die Polygone nicht(echt). *)
lemma "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow> TL = dagList (trapezoidalMap PL)
  \<Longrightarrow> i < length TL \<longrightarrow> (j < length PL \<longrightarrow> \<not>polygonCrossing (PL!j) (TL!i))"     
oops

(*entferne die übrigen strecken die noch innerhalb der Polygone sind*)

(*zeige das keine der Strecken von trapezoidalMap im Polygon sind*)

(*zeige das die trapezoidalMap jetzt eine Einteilung der Freien-Räume innerhalb der rBox ist*)

(*roadMap. Eingabe TrapezodiodamMap T*)

(*beweise das Strecken zwischen RaodMap immer Kollisionsfrei*)



(*alte Definition*)
(*(*The termination argument for followS is based on the fact that the difference
between "xCoord (rightP T)" and  "xCoord Q"  gets smaller in every step*) 
(*dafür müssen aber entweder in dag noch annahmen stecken, annahmen für followS*)
(*functions with conditional patterns are not supported by the code generator.*)
(*fun followS :: "dag \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "followS D T P Q = (if(leftFromPoint (rightP T) Q)
  then(followS D (nextTrapez D (dagList D) T P Q) P Q)
  else ([]))"*)
(*definition followSegment :: "dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "followSegment D P Q = (queryTrapezoidMap D P) # (sortedIntersectTrapez (dagList D) P Q)"*)
(*lemma "queryTrapezoidMap D p = queryTrapezoidMap D q \<Longrightarrow> followSegment D p q = dagList(D)"
  apply (simp only: followSegment_def)
  apply (cases D)
oops*)*)

(*
(*Input: dag(start with rBox) and List of polygons forming a planar subdivision.
Output:  A trapezoid map M in associated search structure dag.*)
fun buildTrapezoidalMap :: "dag \<Rightarrow> (point2d list) list \<Rightarrow> dag" where
  "buildTrapezoidalMap D [] = D"
  |"buildTrapezoidalMap D (P#Pl) = buildTrapezoidalMap (polygonExtendTrapezoidalMap D P) Pl"*)

(*(*gehe von links nach rechts durch die Trapeze, die die Strecke S schneiden.
Input: A Trapezoidal map T, a search structure D, segment PQ
Output: list of trapezoids intersected by PQ *)
fun followSegment :: "dag \<Rightarrow> trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "followSegment D TM T Q = (T # followSegment D (TM) (rightN TM T) Q)"
(*function followSegment :: "dag \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "leftFromPoint (rightP T) (rightP (rightUpperN (dagList D) T p q)) \<or> leftFromPoint (rightP T) (rightP (rightLowerN (dagList D) T p q))
  \<Longrightarrow> followSegment D T p q =
  (if (leftFromPoint (rightP T) q)
    then (T # followSegment D
      (if (pointAboveSegment (rightP T) p q) then (rightUpperN (dagList D) T p q)
      else (rightLowerN (dagList D) T p q)) p q)
  else ([]))"
by (auto, metis leftP leftPRigthFromRightP rightP)*)
(*termination followSegment (*beweise das das nächste Trapez rechts von dem linkem Trapez*)
apply (subgoal_tac "xCoord (leftP t) < xCoord (leftP (queryTrapezoidMap D (rightP t)))")
sorry*)
(*function followSegment :: "dag \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "bla D T p q = (if (leftFromPoint (rightP T) q)
  then (T # followSegment D (queryTrapezoidMap D (Abs_point2d(xCoord (rightP T), lineFunktionY p q (xCoord (rightP T))))) p q)
  else ([]))"
by(auto)*)
lemma "T = queryTrapezoidMap D q \<Longrightarrow> followSegment D T p q = [T]"
  apply (simp)
  apply (safe)
oops*)
end
