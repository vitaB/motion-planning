theory dag
imports norm
begin

(*Defintion für trapez. durch Strecke über dem Trapez, Strecke unter dem Trapez.
linker Endpunkt, rechter Endpunkt*)
typedef trapez = "{p::((point2d*point2d)*(point2d*point2d)*point2d*point2d). True}" by(auto)
definition topT :: "trapez \<Rightarrow> (point2d\<times>point2d)" where  "topT T \<equiv> fst(Rep_trapez T)"
definition bottomT :: "trapez \<Rightarrow> (point2d\<times>point2d)" where "bottomT T \<equiv> fst(snd(Rep_trapez T))"
definition leftP :: "trapez \<Rightarrow> point2d" where "leftP T \<equiv> fst(snd(snd(Rep_trapez T)))"
definition rightP :: "trapez \<Rightarrow> point2d" where "rightP T \<equiv> snd(snd(snd(Rep_trapez T)))"
lemma topTSimp [simp] : "topT (Abs_trapez ((a,b),(c,d),e,f)) = (a,b)" by (simp add: topT_def Abs_trapez_inverse)
lemma bottomTSimp [simp] : "bottomT (Abs_trapez ((a,b),(c,d),e,f)) = (c,d) "by (simp add: bottomT_def Abs_trapez_inverse)
lemma leftPSimp [simp] : "leftP (Abs_trapez ((a,b),(c,d),e,f)) = e" by (simp add: leftP_def Abs_trapez_inverse)
lemma rightPSimp [simp] : "rightP (Abs_trapez ((a,b),(c,d),e,f)) = f" by (simp add: rightP_def Abs_trapez_inverse)
lemma trapezSameCoord [simp]: "(Abs_trapez ((a,b),(c,d),e,f) = Abs_trapez ((a',b'),(c',d'),e',f'))
  \<longleftrightarrow> a=a'\<and> b=b' \<and> c=c' \<and> d=d' \<and> e=e' \<and> f=f'"
  by (metis Abs_trapez_inverse Collect_const UNIV_I fst_conv snd_conv)
lemma trapezSameCoord1 : "(Abs_trapez ((a,b),(c,d),e,f) \<noteq> Abs_trapez ((a',b'),(c',d'),e',f'))
  \<longleftrightarrow> a\<noteq>a'\<or> b\<noteq>b' \<or> c\<noteq>c' \<or> d\<noteq>d' \<or> e\<noteq>e' \<or> f\<noteq>f'" sorry

(*ein Trapez und seine Nachbarn*)
(*record trapezoid = trapez :: trapez
  upRightNeighbor :: "trapez"
  lowerRightNeighbor :: "trapez"
  upLeftNeighbor :: "trapez"
  lowerLeftNeighbor :: "trapez"*)

(*Knoten des graphen kann enweder ein Endpunkt sein, oder ein Segment*)
datatype_new kNode = xNode "point2d" | yNode "(point2d\<times>point2d)"

(*directed acyclic graph*)
(*x-nodes stores a segment endpoint that defines a vertical extension in the trapezoid map,
and has leftChild() and rightChild() pointers to nodes.*)
(*y-node stores a line segment and its children are also recorded by the pointers are aboveChild()
and belowChild() depending on whether the child item is above or below the segment stored at the y-node.*)
datatype_new dag = Tip "trapez" | Node "dag" kNode "dag"


(*Algorithm QueryTrapezoidMap(dag,point2d)
Input: T is the trapezoid map search structure, n is a node in the search structure and p is a query point.
Output:  A pointer to the node in D for the trapezoid containing the point p.*)
fun queryTrapezoidMap :: "dag \<Rightarrow> point2d \<Rightarrow> dag" where
  "queryTrapezoidMap (Tip T) _ = Tip T"
  |"queryTrapezoidMap (Node lf (xNode n) rt) p = 
   (if (xCoord p < xCoord n) then (queryTrapezoidMap lf p) else (queryTrapezoidMap rt p))"
  |"queryTrapezoidMap (Node lf (yNode x) rt) p =
  (*lf ist über dem segment, rt ist unter dem segment*)
   (if (pointAboveSegment (fst x) (snd x) p) then (queryTrapezoidMap lf p) else (queryTrapezoidMap rt p))"


(*Einfacher Fall: allgemeinFall. weder P noch Q sind in T drin, auch nicht an den Ecken*)
definition replaceTrapezSimpA :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "replaceTrapezSimpA  T P Q =
   Node (Tip (Abs_trapez (topT T,(P,Q),P,Q)))
    (yNode (P,Q))
   (Tip (Abs_trapez ((P,Q),bottomT T,P,Q)))"

(*Einfacher Fall: füge Q hinzu, P bereits betrachtet*)
definition replaceTrapezSimpQ :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "replaceTrapezSimpQ T P Q =
    Node (replaceTrapezSimpA T P Q)
      (xNode Q)
    (Tip (Abs_trapez(topT T,bottomT T,Q,rightP T)))"

(*Einfacher Fall: wenn P und Q in T liegen*)
definition replaceTrapezSimp :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "replaceTrapezSimp  T P Q = (
    if((leftP T \<noteq> P \<and> rightP T \<noteq> Q)) (*P und Q sind keine Endpunkte von Trapezen*)
    then (
      Node (Tip(Abs_trapez(topT T,bottomT T,leftP T,P)))
        (xNode P)
        (replaceTrapezSimpQ T P Q)
    ) else( if (leftP T = P \<and> rightP T \<noteq> Q) (*P ist ein Endpunkt, Q nicht*)
        then (replaceTrapezSimpQ T P Q)
        else (if(leftP T \<noteq> P \<and> rightP T = Q) (*Q ist ein Endpunkt, P nicht*)
          then (Node (Tip (Abs_trapez(topT T, bottomT T, leftP T, P)))
            (xNode P)
           (replaceTrapezSimpA T P Q)
           (*P und Q sind Endpunkte*)
           )else (replaceTrapezSimpA T P Q)
      )))"

(*gehe solange von T zum nächsten linken Nachbarn, bis leftP des Trapez über PQ liegt*)
definition "topLeftCorner TM T P Q = P"
(*gehe solange von T zum nächsten rechten Nachbarn, bis rightP des Trapez über PQ liegt*)
definition "topRightCorner TM T P Q = P"
(*gehe solange von T zum nächsten linken Nachbarn, bis leftP des Trapez unter PQ liegt*)
definition "bottomLeftCorner TM T P Q = P"
(*gehe solange von T zum nächsten rechten Nachbarn, bis rightP des Trapez unter PQ liegt*)
definition "bottomRightCorner TM T P Q = P"

(*ersetze mittlere Trapeze, d.h. P liegt in T0, Q liegt in Tn und Trapez Ti soll ersetzt werden*)
definition replaceTrapezM :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
   "replaceTrapezM  T TM P Q =
   Node (Tip (Abs_trapez(topT T,(P,Q),(topLeftCorner TM T P Q), (topRightCorner TM T P Q))))
      (yNode (P,Q))
    (Tip (Abs_trapez((P,Q), bottomT T, (bottomLeftCorner TM T P Q), (bottomRightCorner TM T P Q))))"

definition replaceTrapezFirstY :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "replaceTrapezFirstY T TM P Q =
  Node (Tip (Abs_trapez(topT T, (P,Q), P, (topRightCorner TM T P Q))))
    (yNode (P,Q))
   (Tip (Abs_trapez((P,Q), bottomT T, P, (bottomRightCorner TM T P Q))))"

definition replaceTrapezFirst :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "replaceTrapezFirst T TM P Q = (
  if (leftP T = P) then(replaceTrapezFirstY T TM P Q)
  else (Node (Tip (Abs_trapez(topT T, bottomT T, leftP T, P)))
    (xNode P)
  (replaceTrapezFirstY T TM P Q) ))"

definition replaceTrapezLastY :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
   "replaceTrapezLastY T TM P Q = Node (Tip (Abs_trapez(topT T, (P,Q), topLeftCorner TM T P Q, Q)))
    (yNode (P,Q))
   (Tip (Abs_trapez((P,Q),bottomT T, bottomLeftCorner TM T P Q, Q)))"

definition replaceTrapezLast :: "trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
  "replaceTrapezLast T TM P Q = (
  if (rightP T = Q) then(replaceTrapezLastY T TM P Q)
  else (Node (replaceTrapezLastY T TM P Q)
   (xNode Q)
  (Tip (Abs_trapez(topT T,bottomT T, Q, rightP T)))
  ))"

(*Algorithm replaceTrapez(dag,trapez, trapez list, segment)*)
(*Input: SuchBaum D, Trapez T das ersetz werden soll, Trapezliste TM mit Trapezen die Strecke PQ kreuzt, Strecke PQ
Output: dag welches Trapez T ersetzen soll*)
definition replaceTrapez :: "dag \<Rightarrow> trapez \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> dag" where
"replaceTrapez D T TM P Q = (if (length TM = 1) then (replaceTrapezSimp T P Q)
    else (if (queryTrapezoidMap D P = (Tip T)) then (replaceTrapezFirst T TM P Q)
      else (if (queryTrapezoidMap D Q = (Tip T)) then (replaceTrapezLast T TM P Q)
        else (replaceTrapezM T TM P Q)
      )
    ))"

(*gehe von links nach rechts durch die Trapeze, die die Strecke S schneidet.
Input: A Trapezoidal map T, a search structure D, segment PQ
Output: list of trapezoids intersected by PQ *)
fun followSegment :: "trapez \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "followSegment t a = (if (pointInTrapez t a)
  then (t) else (t # followSegment(trapezRightAdjacent t) a))"

(*gib eine List mit trapezen zurück die das Segment PQ schneiden
Input: suchBaum D, Segment PQ
Output: liste mit trapezen*)
fun intersectTrapez :: "dag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
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

(*überprüfe ob durch alle Ecken in TrapezoidalMap ein "Teil-slab geht"*)
(*vertikale Strecken einzeichnen, die durch Eckpunkte gehen
Eingabe Menge der Segmente(polygone ohne cyclePath) und rBox*)
(*fun slabs :: "point2d list \<Rightarrow> point2d list \<Rightarrow> point2d list" where
  "slabs [] R  = []"
  | "slabs (x#xs) R = [Abs_point2d(xCoord x, yCoord (hd (yCoordSort R))),
    Abs_point2d(xCoord x, yCoord (last (yCoordSort R)))] @ slabs xs R"*)


(*kleiner Test*)
definition "t0 \<equiv> Abs_trapez ((Abs_point2d(1,3),Abs_point2d(4,4)),(Abs_point2d(0,0),Abs_point2d(3,0)),Abs_point2d(0,0),Abs_point2d(4,4))"
definition "t1 \<equiv> Abs_trapez ((Abs_point2d(1,3),Abs_point2d(4,4)),(Abs_point2d(0,0),Abs_point2d(3,0)),Abs_point2d(0,0),Abs_point2d(2,1))"
definition "t2 \<equiv> Abs_trapez ((Abs_point2d(1,3),Abs_point2d(4,4)),(Abs_point2d(2,1),Abs_point2d(3,0)),Abs_point2d(2,1),Abs_point2d(3,0))"
definition "t3 \<equiv> Abs_trapez ((Abs_point2d(2,1),Abs_point2d(3,0)),(Abs_point2d(0,0),Abs_point2d(3,0)),Abs_point2d(2,1),Abs_point2d(3,0))"
definition "t4 \<equiv> Abs_trapez ((Abs_point2d(1,3),Abs_point2d(4,4)),(Abs_point2d(0,0),Abs_point2d(3,0)),Abs_point2d(3,0),Abs_point2d(4,4))"
lemma  "replaceTrapez (Tip t0) t0 [t0] (Abs_point2d(2,1)) (Abs_point2d(3,0)) =
  Node (Tip t1) (xNode (Abs_point2d(2,1))) (Node (Node (Tip t2) (yNode ((Abs_point2d(2,1)),(Abs_point2d(3,0)))) (Tip t3)) (xNode (Abs_point2d(3,0))) (Tip t4))"
  apply (simp add: replaceTrapez_def)
  apply (simp only: replaceTrapezSimp_def)
  apply (simp only: t0_def t1_def t2_def t3_def t4_def leftPSimp rightPSimp topTSimp bottomTSimp)
  apply (simp)
  apply (simp add: replaceTrapezSimpQ_def replaceTrapezSimpA_def)
done
end
