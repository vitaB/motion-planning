theory trapezoidalMap
imports tDag
begin

(*gehe solange bis zum nächsten Nachbarn bis gesuchte Ecke gefunden ist
Input: funktion die linke/rechte Ecke vom Trapez gibt, Trapez-List,
  Entscheidung Trapez-Ecke über/unter segment PQ liegt, Strecke PQ
Output: nächste linke/rechte Ecke die über dem Segment P/Q liegt*)
fun nextCorner :: "(trapez \<Rightarrow> point2d) \<Rightarrow> trapez list \<Rightarrow> (point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool) \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "nextCorner f [TM] _  _ _ = f TM"
  |" nextCorner f (TM#TS) g P Q = (if (g (f TM) P Q) then (f TM) else (nextCorner f TS g P Q))"

(*gehe solange von T zum nächsten linken Nachbarn, bis leftP des Trapez über PQ liegt*)
definition topLeftCorner:: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "topLeftCorner TM T P Q = nextCorner leftP (dropWhile (trapezNotEq T) (rev TM)) pointAboveSegment P Q"
(*gehe solange von T zum nächsten rechten Nachbarn, bis rightP des Trapez über PQ liegt*)
definition topRightCorner :: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "topRightCorner TM T P Q = nextCorner rightP (dropWhile (trapezNotEq T) TM) pointAboveSegment P Q"
(*gehe solange von T zum nächsten linken Nachbarn, bis leftP des Trapez unter PQ liegt*)
definition bottomLeftCorner :: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "bottomLeftCorner TM T P Q = nextCorner leftP (dropWhile (trapezNotEq T) (rev TM)) pointBelowSegment P Q"
(*gehe solange von T zum nächsten rechten Nachbarn, bis rightP des Trapez unter PQ liegt*)
definition bottomRightCorner :: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d" where
  "bottomRightCorner TM T P Q = nextCorner rightP (dropWhile (trapezNotEq T) TM) pointBelowSegment P Q"

(*Algorithm QueryTrapezoidMap(dag,point2d)
Input: T is the trapezoid map search structure, n is a node in the search structure and p is a query point.
Output:  A pointer to the node in D for the trapezoid containing the point p.*)
fun queryTrapezoidMap :: "dag \<Rightarrow> point2d \<Rightarrow> trapez" where
  "queryTrapezoidMap (Tip T) _ =  T"
  |"queryTrapezoidMap (Node lf (xNode n) rt) p = 
   (if (xCoord p < xCoord n) then (queryTrapezoidMap lf p) else (queryTrapezoidMap rt p))"
  |"queryTrapezoidMap (Node lf (yNode x) rt) p =
  (*lf ist über dem segment, rt ist unter dem segment*)
   (if (pointAboveSegment p (fst x) (snd x)) then (queryTrapezoidMap lf p) else (queryTrapezoidMap rt p))"


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

(*gehe von links nach rechts durch die Trapeze, die die Strecke S schneiden.
Input: A Trapezoidal map T, a search structure D, segment PQ
Output: list of trapezoids intersected by PQ *)
function followSegment :: "dag \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "followSegment D t a = (if (xCoord a > xCoord (leftP t))
  then (t # followSegment D (queryTrapezoidMap D (rightP t)) a) else ([]))"
by (auto)

(*gib eine Liste mit trapezen zurück die das Segment PQ schneiden
Input: suchBaum D, Segment PQ
Output: liste mit trapezen*)
definition intersectTrapez :: "dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "intersectTrapez D p q = followSegment D (queryTrapezoidMap D p) q"

(*ersetzt alle übergebenen Trapeze im dag durch neue Trapeze, die mit PQ erstellt wurden
Input : suchBaum D, 2 mal Liste mit Trapezen die ersetzt werden sollen,Segment PQ
Output: neues Dag, nachdem alle Trapeze ersetzt wurden*)
fun replaceDag :: "dag \<Rightarrow> trapez list \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "replaceDag D [] _ _ _ = D"
  | "replaceDag D (T#Ts) TM P Q = replaceDag (replaceTip T (newDag D T TM P Q ) D) Ts TM P Q"

(*erneure dag nach dem hinzufügen eines segments*)
definition addSegmentToTrapezoidalMap :: "dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "addSegmentToTrapezoidalMap D P Q \<equiv> replaceDag D (intersectTrapez D P Q) (intersectTrapez D P Q) P Q"

(*hier müssen die eigentlichen Beweise stehen!*)

(*zeige das jedes neue Trapez ein convexes Polygon ist*)


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
(*
(*Input: dag(start with rBox) and List of polygons forming a planar subdivision.
Output:  A trapezoid map M in associated search structure dag.*)
fun buildTrapezoidalMap :: "dag \<Rightarrow> (point2d list) list \<Rightarrow> dag" where
  "buildTrapezoidalMap D [] = D"
  |"buildTrapezoidalMap D (P#Pl) = buildTrapezoidalMap (polygonExtendTrapezoidalMap D P) Pl"*)
end
