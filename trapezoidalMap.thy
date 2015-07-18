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
definition segmentExtendTrapezoidalMap :: "dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "segmentExtendTrapezoidalMap D P Q \<equiv> replaceDag D (intersectTrapez D P Q) (intersectTrapez D P Q) P Q"

(*Input: List of line segments(one Polygon) forming a planar subdivision.
Output:  A trapezoid map M in associated search structure dag.*)
fun polygonExtendTrapezoidalMap :: "dag \<Rightarrow> point2d list \<Rightarrow> dag" where
  "polygonExtendTrapezoidalMap D [] = D"
  | "polygonExtendTrapezoidalMap D [q] = D"
  | "polygonExtendTrapezoidalMap D (p#q#xs) =
  polygonExtendTrapezoidalMap (segmentExtendTrapezoidalMap D (leftPSegment p q) (rightPSegment p q)) (q#xs)"

(*Input: dag(start with rBox) and List of polygons forming a planar subdivision.
Output:  A trapezoid map M in associated search structure dag.*)
fun buildTrapezoidalMap :: "dag \<Rightarrow> (point2d list) list \<Rightarrow> dag" where
  "buildTrapezoidalMap D [] = D"
  |"buildTrapezoidalMap D (P#Pl) = buildTrapezoidalMap (polygonExtendTrapezoidalMap D P) Pl"

definition trapezoidalMap :: "(point2d list) list \<Rightarrow> dag" where
  " pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow>
  trapezoidalMap PL \<equiv> buildTrapezoidalMap (Tip (rBoxTrapez PL)) PL"

(*zeige das jedes Trapez ein convexes Polygon ist*)
lemma "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow> TL = dagList (trapezoidalMap PL)
  \<Longrightarrow> i < length TL \<longrightarrow> cPolygon (cyclePath (trapezToPointList (TL!i)))"
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





(*kleiner Test*)
definition "t0 \<equiv> Abs_trapez ((Abs_point2d(1,3),Abs_point2d(4,4)),(Abs_point2d(0,0),Abs_point2d(3,0)),Abs_point2d(0,0),Abs_point2d(4,4))"
definition "t1 \<equiv> Abs_trapez ((Abs_point2d(1,3),Abs_point2d(4,4)),(Abs_point2d(0,0),Abs_point2d(3,0)),Abs_point2d(0,0),Abs_point2d(2,1))"
definition "t2 \<equiv> Abs_trapez ((Abs_point2d(1,3),Abs_point2d(4,4)),(Abs_point2d(2,1),Abs_point2d(3,0)),Abs_point2d(2,1),Abs_point2d(3,0))"
definition "t3 \<equiv> Abs_trapez ((Abs_point2d(2,1),Abs_point2d(3,0)),(Abs_point2d(0,0),Abs_point2d(3,0)),Abs_point2d(2,1),Abs_point2d(3,0))"
definition "t4 \<equiv> Abs_trapez ((Abs_point2d(1,3),Abs_point2d(4,4)),(Abs_point2d(0,0),Abs_point2d(3,0)),Abs_point2d(3,0),Abs_point2d(4,4))"
lemma  "newDag (Tip t0) t0 [t0] (Abs_point2d(2,1)) (Abs_point2d(3,0)) =
  Node (Tip t1) (xNode (Abs_point2d(2,1))) (Node (Node (Tip t2) (yNode ((Abs_point2d(2,1)),(Abs_point2d(3,0)))) (Tip t3)) (xNode (Abs_point2d(3,0))) (Tip t4))"
  apply (simp add: newDag_def)
  apply (simp only: newDagSimp_def)
  apply (simp only: t0_def t1_def t2_def t3_def t4_def leftPSimp rightPSimp topTSimp bottomTSimp)
  apply (simp)
  apply (simp add: newDagSimpQ_def newDagSimpA_def)
done
fun lDag :: "dag \<Rightarrow> dag" where
  "lDag (Node Tl x Tr) = Tl"
fun rDag :: "dag \<Rightarrow> dag" where
  "rDag (Node Tl x Tr) = Tr"
definition "dag1 = Node (Tip t0) (xNode (Abs_point2d(1,3))) (Tip t0)"
lemma "replaceTip t0 (newDag (Tip t0) t0 [t0] (Abs_point2d(2,1)) (Abs_point2d(3,0))) dag1 
  = Node ((newDag (Tip t0) t0 [t0] (Abs_point2d(2,1)) (Abs_point2d(3,0)))) (xNode (Abs_point2d(1,3))) ((newDag (Tip t0) t0 [t0] (Abs_point2d(2,1)) (Abs_point2d(3,0))))"
  apply (simp add: dag1_def)
done
end
