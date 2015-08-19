theory roadMap
imports trapezoidalMap
begin

(*beweise dass wenn Trapeze benachbart, dann kommt man immer von rechte ecke zu der anderen rechten Ecke
ohne überschneidung von Polygonen*)
lemma "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow> rBoxTrapezS (concat PL) R \<Longrightarrow>
  \<not>cyclePathsIntersect PL \<Longrightarrow> D = buildTrapezoidalMap R PL \<Longrightarrow> \<forall> i j k. (i \<noteq> j \<and> i < length (tDagList D)
  \<and> j < length (tDagList D) \<and> trapezNeighbor ((tDagList D)!i) ((tDagList D)!j) \<longrightarrow>
  \<not>lineCyclePathInters (PL!k) (rightP ((tDagList D)!i)) (rightP ((tDagList D)!i)))"
  (*intersectFree nur wenn ich nicht die Knotenpunkte nehme!*)    
oops

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
