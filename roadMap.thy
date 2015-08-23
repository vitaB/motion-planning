theory roadMap
imports trapezoidalMap
begin

(*jede Strecke von der linken Vertikale zur der rechten Vertikal eines beliebigen Trapezes
  aus der TrapezoidalMap schneidet keine der Polygone aus der Polygonen-Liste*)
lemma segmentInTrapezIntersectFree: "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow>
  uniqueXCoord (concat PL) \<Longrightarrow> rBoxTrapezS (concat PL) R
  \<Longrightarrow> polygonsDisjoint PL \<Longrightarrow> D = buildTrapezoidalMap R PL \<Longrightarrow> 
  i < length (tDagList D) \<Longrightarrow> k < length (tDagList D) \<Longrightarrow>
  A \<noteq> leftP ((tDagList D)!i) \<Longrightarrow> B \<noteq> rightP ((tDagList D)!i) \<Longrightarrow>
  (pointOnLeftT ((tDagList D)!i) A \<Longrightarrow> pointOnRightT ((tDagList D)!i) B \<Longrightarrow>
    \<not>lineCyclePathInters (cyclePath (PL!k)) A C)"
oopss

(*es gibt einen Kanten-Zug für zwei beliebige benachbarten Trapeze aus der TrapezoidalMap,
  von der linken Vertikale zu der rechten Vertikale, so dass der Kanten-Zug
  keine der Polygone aus der Polygonen-Liste schneidet*)
lemma "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow> rBoxTrapezS (concat PL) R
  \<Longrightarrow> polygonsDisjoint PL \<Longrightarrow> D = buildTrapezoidalMap R PL \<Longrightarrow> 
  i < length (tDagList D) \<Longrightarrow> j < length (tDagList D) \<Longrightarrow> k < length PL \<Longrightarrow>
  A \<noteq> leftP ((tDagList D)!i) \<Longrightarrow> C \<noteq> rightP ((tDagList D)!j) \<Longrightarrow>
  trapezNeighbor ((tDagList D)!i) ((tDagList D)!j) \<Longrightarrow> 
  (pointOnLeftT ((tDagList D)!i) A \<Longrightarrow> pointOnRightT ((tDagList D)!j) C \<Longrightarrow>
   \<exists> B. \<not>cyclePathIntersect(cyclePath (PL!k)) [A,B,C])"
oops



(*beweise dass wenn Trapeze benachbart, dann kommt man immer von rechten ecke zu der anderen rechten Ecke
ohne überschneidung von Polygonen*)
(*lemma "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow> rBoxTrapezS (concat PL) R
  \<Longrightarrow> polygonsDisjoint PL \<Longrightarrow> D = buildTrapezoidalMap R PL \<Longrightarrow>
  \<forall> i j k. ((i \<noteq> j \<and> i < length (tDagList D) \<and> j < length (tDagList D) \<and> k < length (tDagList D)
    \<and> trapezNeighbor ((tDagList D)!i) ((tDagList D)!j))
    \<longrightarrow> (pointOnRightT ((tDagList D)!i) P \<and>
    \<not>lineCyclePathInters (PL!k) (rightP ((tDagList D)!i)) (rightP ((tDagList D)!i))))"
  (*intersectFree nur wenn ich nicht die Knotenpunkte nehme!*)  
  (*nehme Punkte die auf der vertikalen liegen und überprüfe ob diese über rightP oder unter liegen müssen
    benutze dafür den test auf die gemeinsaben topT oder bottomT*)  
oops*)

(*rückgabe als Baum nur möglich, wenn man ein leeren Tip Knoten einfügt*)
fun freeSpace :: "tDag \<Rightarrow> (point2d list) list \<Rightarrow> tDag" where
  "freeSpace (Tip R) PL = Tip R" (*überprüfe of bottomT und topT zum selben Polygon gehören*)
  | "freeSpace (Node Tl n Tr) PL = Node (freeSpace Tl PL) n (freeSpace Tr PL)"

(*entferne die übrigen strecken die noch innerhalb der Polygone sind*)
definition computeFreeSpace :: "tDag \<Rightarrow> (point2d list) list \<Rightarrow> tDag" where
  "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow> rBoxTrapezS (concat PL) R \<Longrightarrow>
  polygonsDisjoint PL \<Longrightarrow> D = addPolygonsToTrapezoidalMap (Tip R) PL \<Longrightarrow>
  computeFreeSpace D PL \<equiv> freeSpace D PL"

(*zeige das keine der Strecken von trapezoidalMap im Polygon sind*)

(*zeige das die trapezoidalMap jetzt eine Einteilung der Freien-Räume innerhalb der rBox ist*)

(*linke und rechte Strecke von trapezen schneiden die Polygone nicht(echt).
dafür müsste man jedoch leftT und rightT ausrechnen. einfacher wäre es evtl., wenn man impliziet zeigt
dass leftT und rightT vertikale(müssen die das sein?) sind und von topT und bottomT begrenzt werden,
d.h. andere segmente nicht schneiden*)
lemma "pointLists L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> uniqueXCoord L \<Longrightarrow> rBoxS R L \<Longrightarrow>
  TL = tDagList (simpTrapezoidalMap R P)
  \<Longrightarrow> i < length TL \<Longrightarrow> j < length TL \<Longrightarrow> \<not>polygonCrossing (PL!j) (TL!i)" (*lineCyclePathInters*)  
oops

(*beweise das Strecken zwischen RaodMap immer Kollisionsfrei*)

end
