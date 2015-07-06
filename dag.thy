theory dag
imports polygon
begin

(*Defintion für trapez. durch Strecke über dem Trapez, Strecke unter dem Trapez.
linker Endpunkt, rechter Endpunkt*)
record trapez = topT :: "point2d\<times>point2d"
  bottomT :: "point2d\<times>point2d"
  leftp :: point2d
  rightp :: point2d

(*ein Trapez und seine Nachbarn*)
record trapezoid = trapez :: trapez
  neighbor :: "trapez list"

(*Knoten des graphen kann enweder ein Endpunkt sein, oder ein Segment*)
datatype_new kNode = xNode "point2d" | yNode "(point2d\<times>point2d)"

(*directed acyclic graph*)
(*x-nodes stores a segment endpoint that defines a vertical extension in the trapezoid map,
and has leftChild() and rightChild() pointers to nodes.*)
(*y-node stores a line segment and its children are also recorded by the pointers are aboveChild()
and belowChild() depending on whether the child item is above or below the segment stored at the y-node.*)
datatype_new dag = Tip "trapezoid" | Node "dag" kNode "dag"

(*Algorithm QueryTrapezoidMap( n, p)
Input: T is the trapezoid map search structure, n is a 
   node in the search structure and p is a query point.
Output:  A pointer to the node in D for the trapezoid 
   containing the point p.*)
fun queryTrapezoidMap :: "dag \<Rightarrow> point2d \<Rightarrow> trapezoid" where
  "queryTrapezoidMap (Tip n) _ = n"
  |"queryTrapezoidMap (Node lf (xNode n) rt) p = 
   (if (xCoord p < xCoord n) then (queryTrapezoidMap lf p) else (queryTrapezoidMap rt p))"
  |"queryTrapezoidMap (Node lf (yNode x) rt) p =
  (*lf ist über dem segment, rt ist unter dem segment*)
   (if (pointAboveSegment (fst x) (snd x) p) then (queryTrapezoidMap lf p) else (queryTrapezoidMap rt p))"
(*  |"queryTrapezoidMap (Node  x b) N p = "*)




(*trapezoidal map T, searchStructure D, segment s*)
fun followSegment :: "trapezoid list \<Rightarrow> dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d list" where
  "followSegment (ti#T) A B =
    (if (leftFromSegment A B (rightp ti)) then (
      if (crossing A B p r) then ()
      else ())
    else (rest der trapezoidal anhängen))"

(*vertikale Strecken einzeichnen, die durch Eckpunkte gehen
Eingabe Menge der Segmente(polygone ohne cyclePath) und rBox*)
fun slabs :: "point2d list \<Rightarrow> point2d list \<Rightarrow> point2d list" where
  "slabs [] R  = []"
  | "slabs (x#xs) R = [Abs_point2d(xCoord x, yCoord (hd (yCoordSort R))),
    Abs_point2d(xCoord x, yCoord (last (yCoordSort R)))] @ slabs xs R"

end
