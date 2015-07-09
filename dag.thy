theory dag
imports polygon
begin

definition uniqueXCoord :: "point2d list \<Rightarrow> bool" where
  "uniqueXCoord L \<equiv> \<forall> a b. a \<noteq> b \<longrightarrow> xCoord (L!a) \<noteq> xCoord (L!b)"

(*4eckige Box um pointListe herum ist selbst eine pointList*)
lemma rBoxPointList: "pointList (concat PL) \<Longrightarrow> pointList(
  [Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1, yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (last (yCoordSort (concat PL))) + 1),
  Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1,yCoord (last (yCoordSort (concat PL))) + 1)])"
sorry

(*4eckige Box um pointListen herum*)
definition rBox :: "(point2d list) list \<Rightarrow> point2d list" where
  "pointList (concat PL) \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow> rBox PL \<equiv>
  cyclePath([Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1, yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (hd (yCoordSort (concat PL))) - 1),
  Abs_point2d(xCoord (last (xCoordSort (concat PL))) + 1,yCoord (last (yCoordSort (concat PL))) + 1),
  Abs_point2d(xCoord (hd (xCoordSort (concat PL))) - 1,yCoord (last (yCoordSort (concat PL))) + 1)])"

(*ersetzte den Term Polygon im Satz*)
lemma rBoxPoly [simp] : "pointList (concat PL) \<Longrightarrow>
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

(*rBox ist ein Convexes Polygon*)
lemma rBoxConvex : "pointList (concat PL) \<Longrightarrow> polygon (rBox PL)"  
oops

(*alle Punkte von PL sind innerhalb von rBox PL*)
lemma "pointList (concat PL) \<Longrightarrow> \<forall> a \<in> set L. pointInsidePolygon (rBox PL) a"
  apply (cut_tac PL=PL in rBoxConvex, assumption)
oops

(*Defintion für trapez. durch Strecke über dem Trapez, Strecke unter dem Trapez.
linker Endpunkt, rechter Endpunkt*)
record trapez = topT :: "point2d\<times>point2d"
  bottomT :: "point2d\<times>point2d"
  leftP :: point2d
  rightP :: point2d
definition newTrapez :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez" where
  "newTrapez a b c d e f \<equiv> \<lparr>topT=(a,b), bottomT=(c,d), leftP= e, rightP=f\<rparr>"

definition t1 :: trapez where
  "t1 \<equiv> (|topT =(Abs_point2d(1,1),Abs_point2d(1,1)), bottomT =(Abs_point2d(1,1),Abs_point2d(1,1)), leftP =Abs_point2d(1,1), rightP=Abs_point2d(1,1)|)"

(*ein Trapez und seine Nachbarn*)
record trapezoid = trapez :: trapez
  upRightNeighbor :: "trapez"
  lowerRightNeighbor :: "trapez"
  upLeftNeighbor :: "trapez"
  lowerLeftNeighbor :: "trapez"
definition tr1 :: trapezoid where
  "tr1 \<equiv> \<lparr>trapez = t1,
  upRightNeighbor= t1,lowerRightNeighbor=t1, upLeftNeighbor=t1,lowerLeftNeighbor=t1 \<rparr>"

(*Knoten des graphen kann enweder ein Endpunkt sein, oder ein Segment*)
datatype_new kNode = xNode "point2d" | yNode "(point2d\<times>point2d)"
definition node1 :: kNode where
  "node1 \<equiv> xNode (Abs_point2d(1,1))"
definition node2 :: kNode where
  "node2 \<equiv> yNode (Abs_point2d(1,1), Abs_point2d(1,1))"

(*directed acyclic graph*)
(*x-nodes stores a segment endpoint that defines a vertical extension in the trapezoid map,
and has leftChild() and rightChild() pointers to nodes.*)
(*y-node stores a line segment and its children are also recorded by the pointers are aboveChild()
and belowChild() depending on whether the child item is above or below the segment stored at the y-node.*)
datatype_new dag = Tip "trapez" | Node "dag" kNode "dag"

(*Algorithm QueryTrapezoidMap( n, p)
Input: T is the trapezoid map search structure, n is a 
   node in the search structure and p is a query point.
Output:  A pointer to the node in D for the trapezoid 
   containing the point p.*)
fun queryTrapezoidMap :: "dag \<Rightarrow> point2d \<Rightarrow> dag" where
  "queryTrapezoidMap (Tip n) _ = Tip n"
  |"queryTrapezoidMap (Node lf (xNode n) rt) p = 
   (if (xCoord p < xCoord n) then (queryTrapezoidMap lf p) else (queryTrapezoidMap rt p))"
  |"queryTrapezoidMap (Node lf (yNode x) rt) p =
  (*lf ist über dem segment, rt ist unter dem segment*)
   (if (pointAboveSegment (fst x) (snd x) p) then (queryTrapezoidMap lf p) else (queryTrapezoidMap rt p))"

definition dag1 :: dag where
  "dag1 \<equiv> Node (Tip t1) node1 (Node (Tip t1) node2 (Tip t1))"

(*allgemeinFall. weder P noch Q sind in T drin*)
fun replaceTrapezA :: "dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "replaceTrapezA (Tip T) P Q =
   Node (Tip \<lparr>topT=topT T, bottomT=(P,Q), leftP=P, rightP=Q\<rparr>)
    (yNode (P,Q))
   (Tip \<lparr>topT=(P,Q), bottomT=bottomT T, leftP=P, rightP=Q\<rparr>)"

fun replaveTrapezQ :: "dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "replaveTrapezQ (Tip T) P Q =
    Node (replaceTrapezA (Tip T) P Q)
      (xNode Q)
    (Tip \<lparr>topT=(topT T), bottomT=(bottomT T), leftP=Q, rightP=(rightP T)\<rparr>)"

(*einfacher Fall, wenn P und Q in Tip T liegen*)
fun replaceTrapez :: "dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "replaceTrapez (Tip T) P Q = (
    if(leftP T \<noteq> P \<and> rightP T \<noteq> Q) (*P und Q sind keine Endpunkte von Trapezen*)
    then (
      Node (Tip\<lparr>topT=(topT T), bottomT=(bottomT T), leftP=(leftP T), rightP=P\<rparr>)
        (xNode P)
        (replaveTrapezQ (Tip T) P Q)
    ) else( if (leftP T = P \<and> rightP T \<noteq> Q) (*P ist ein Endpunkt, Q nicht*)
        then (replaveTrapezQ (Tip T) P Q)
        else (if(leftP T \<noteq> P \<and> rightP T = Q) (*Q ist ein Endpunkt, P nicht*)
          then (Node (Tip \<lparr>topT=(topT T), bottomT=(bottomT T), leftP=leftP T, rightP=P\<rparr>)
            (xNode P)
           (replaceTrapezA (Tip T) P Q)
           (*P und Q sind Endpunkte*)
           )else (replaceTrapezA (Tip T) P Q)
      )
    )
    )"

(*inkrementell. aber wie?*)
(*ersetze mittlere Trapeze, d.h. P liegt in T0, Q liegt in Tn und Trapez Ti soll ersetzt werden*)
fun replaceTrapezM :: "dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
   "replaceTrapezM (Tip T) P Q =(
   if (pointAboveSegment P Q (leftP T))
   then (Node (Tip \<lparr>topT=topT T, bottomT=(P,Q), leftP=P, rightP=rightP T\<rparr>)
      (yNode (P,Q))
    (Tip \<lparr>topT=(P,Q), bottomT=bottomT T, leftP=leftP T, rightP=\<rparr>))
   else (Tip T))"

(*gehe von links nach rechts durch die Trapeze, die die Strecke S schneidet.
Input: A Trapezoidal map T, a search structure D, segment PQ
Output: list of trapezoids intersected by PQ *)
fun followSegment :: "trapezoid \<Rightarrow> point2d \<Rightarrow> trapezoid list" where
  "followSegment t a = (if (pointInTrapez t a)
  then (t) else (t # followSegment(trapezRightAdjacent t) a))"

(*gib eine List mit trapezen zurück die das Segment PQ schneiden
Input: suchBaum Da, Segment PQ
Output: liste mit trapezen*)
fun intersectTrapez :: "dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapezoid list" where
  "intersectTrapez D p q = (
    if (queryTrapezoidMap D p = queryTrapezoidMap D q) then ([queryTrapezoidMap D p])
    else ( followSegment (queryTrapezoidMap D (leftPSegment p q)) (rightPSegment p q) )
    )"


(*Input: S is the set of line segments forming a planar subdivision.
Output:  A trapezoid map M and an associated search structure M.*)
fun buildTrapezoidalMap :: "dag \<Rightarrow> " where
  "buildTrapezoidalMap = "
  | "buildTrapezoidalMap T (p#q#xs) = buildTrapezoidalMap (replaceTrapez (intersectTrapez T p q)) xs"


(*trapezoidal map T, searchStructure D, segment s*)
(*fun followSegment :: "trapezoid list \<Rightarrow> dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d list" where
  "followSegment (ti#T) A B =
    (if (leftFromSegment A B (rightp ti)) then (
      if (crossing A B p r) then ()
      else ())
    else (rest der trapezoidal anhängen))"*)

(*vertikale Strecken einzeichnen, die durch Eckpunkte gehen
Eingabe Menge der Segmente(polygone ohne cyclePath) und rBox*)
fun slabs :: "point2d list \<Rightarrow> point2d list \<Rightarrow> point2d list" where
  "slabs [] R  = []"
  | "slabs (x#xs) R = [Abs_point2d(xCoord x, yCoord (hd (yCoordSort R))),
    Abs_point2d(xCoord x, yCoord (last (yCoordSort R)))] @ slabs xs R"

end
