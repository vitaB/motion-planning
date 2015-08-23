theory trapezoidalMap
imports tDag (*"~~/src/HOL/Library/Multiset"*)
begin

(*zwei Trapeze sind benachbart entland der Strecke PQ, wenn :
  - die linke Ecke eines Trapezes gleich der rechten Ecke des anderen Trapezes
  - topT gleich sind, falls PQ über rightPT bzw. bottomT gleich sind, falls PQ unter rightP.*)
definition neighborAlongSeg:: "trapez \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "neighborAlongSeg T Ts P Q \<equiv> rightP T = leftP Ts \<and>
  ((rightTurn P Q (rightP T) \<and> topT T = topT Ts) \<or> (leftTurn P Q (rightP T) \<and> bottomT T = bottomT Ts))"
lemma neighborTrapezSame [dest] : "isTrapez T \<Longrightarrow> neighborAlongSeg T T P Q \<Longrightarrow> False"
  by (auto simp add: neighborAlongSeg_def,(metis leftFromPoint_def less_irrefl trapezNeighbour2)+)


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
(*wenn ein Trapez T in Dag D, dann muss es ein Punkt P geben um mit T mit queryTrapezoidMap D P zufinden
stimmt jedoch nur, wenn queryTrapezoidMap nach tDagOrdMap aufgebaut ist!*)
lemma queryTrapezoidMapComplete : "tipInDag T D \<longleftrightarrow> (\<exists> P. T = (queryTrapezoidMap D P))"
oops
(*jedes Trapez was mit queryTrapezoidMap gefunden wird, muss auch mit tipInDag gefunden werden können*)
lemma queryTrapezoidMapInDag: "tipInDag (queryTrapezoidMap D P) D"
sorry


(*****create new Dag to replace intersected Trapez*)
(*Einfacher Fall: allgemeinFall*)
definition newDagSimpA :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "newDagSimpA T P Q =
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
(*stimmt nur wenn tDag eine echte TrapezoidalMap*)
lemma "\<forall> a \<in> set (tDagList (newDag D T TM P Q)). a \<notin> set(tDagList D)"
oops


(*****Find and replace Segment which intersected from added Segment*)
(*gib eine Liste mit trapezen zurück die das Segment PQ schneiden. Reihenfolge von links nach rechts
Input: suchBaum D, trapez list ist nach x-Coord von leftP sortiert, Start Trapez(in dem sich P befindet), Segment PQ
Output: liste mit trapezen*)
(*man verpasst kein Nachbar! weil immer der nächste Nachbar gefunden wird, bevor man zu den zweitem kommen kann!*)
fun followSegment :: "tDag \<Rightarrow> trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where 
  "followSegment _ [] _ _ _ = []"
  | "followSegment D (Ts#TM) T P Q = (if (xCoord Q \<ge> xCoord (rightP T) \<and> neighborAlongSeg T Ts P Q)
    then (Ts # (followSegment D TM Ts P Q)) else (followSegment D TM T P Q))"

(*gib eine trapezliste, die on PQ geschnitten werden.*)
definition intersectedTrapez :: "tDag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "intersectedTrapez D P Q = (queryTrapezoidMap D P) #
  (followSegment D (sortedTrapez (tDagList D)) (queryTrapezoidMap D P) P Q)"
(*wenn p und q im selben Trapez, dann ist length intersectedTrapez = 1*)
lemma oneIntersectedTrapez : "pointInDag D p \<Longrightarrow> pointInDag D q \<Longrightarrow> queryTrapezoidMap D p = queryTrapezoidMap D q \<Longrightarrow>
  intersectedTrapez D p q = [queryTrapezoidMap D q]"
  apply (simp add: intersectedTrapez_def)
  apply (cases D, safe)
    (*Case D = Tip x*)
    apply (subgoal_tac "neighborAlongSeg x1 x1 p q = False", simp add: sortedTrapez_def, metis neighborTrapezSame)
    (*Case D = tl kNode tr*)
    apply (simp add: sortedTrapez_def)
oops

(*intersectedTrapez gibt eine Liste mit echten Nachbarn entlang PQ zurück, dass von P und Q begrenzt ist*)
lemma intersectedTrapezComp : "leftFromPoint P Q \<Longrightarrow> pointInDag D P \<Longrightarrow> pointInDag D Q \<Longrightarrow>
  TM = intersectedTrapez D P Q \<Longrightarrow> (\<forall> i < length TM - 1. neighborTrapez (TM!i) (TM!Suc i) P Q)
  \<and> hd TM = queryTrapezoidMap D P \<and> TM!(length TM - 1) = queryTrapezoidMap D Q"
sorry

(*ersetzt alle übergebenen Trapeze im tDag durch neue Trapeze, die mit PQ erstellt wurden
Input : suchBaum D, 2 mal Liste mit Trapezen die ersetzt werden sollen,Segment PQ
Output: neues Dag, nachdem alle Trapeze ersetzt wurden*)
fun replaceDag :: "tDag \<Rightarrow> trapez list \<Rightarrow> trapez list \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "replaceDag D [] _ _ _ = D"
  | "replaceDag D (T#Ts) TM P Q = replaceDag (replaceTip T (newDag D T TM P Q ) D) Ts TM P Q"


(******add Segment to trapezoidal-map*)
(*erneure tDag nach dem hinzufügen eines segments*)
definition addSegmentToTrapezoidalMap :: "tDag \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> tDag" where
  "leftFromPoint P Q \<Longrightarrow> addSegmentToTrapezoidalMap D P Q \<equiv>
    replaceDag D (intersectedTrapez D P Q) (intersectedTrapez D P Q) P Q"

(*füge Segment in rBox ein*)
(*wenn Segment in trapezoidalMap aufgenommen wird, sind alle neuen Trapeze echte Trapeze*)
lemma "leftFromPoint P Q \<Longrightarrow> rBoxTrapezS [P,Q,a] R \<Longrightarrow>  D=(addSegmentToTrapezoidalMap (Tip R) P Q)
  \<Longrightarrow> i<length(tDagList D) \<Longrightarrow> isTrapez ((tDagList D)!i)"
  apply (simp add: addSegmentToTrapezoidalMap_def intersectedTrapez_def sortedTrapez_def)
  apply (subgoal_tac "\<not>neighborAlongSeg R R P Q", simp)
  apply (simp add: newDag_def newDagSimp_def)
  apply (subgoal_tac "leftP R \<noteq> P \<and> rightP R \<noteq> Q", simp add: newDagSimpQ_def newDagSimpA_def)
  apply (safe)
  (*(*Try all 4*)
  apply (case_tac "i=0")
    apply (simp add: isTrapez_def)
    apply (simp add: rBoxTrapezS_def, erule_tac x=0 in allE, simp add: pointInRBox_def, safe)
    apply (metis leftP leftP_def rightP rightP_def)
    apply (metis isTrapez_def leftP leftP_def leftRightTurn pointInRBox_def rBoxIsTrapez1 rightTurnRotate topT topT_def)
    apply (metis bottomT bottomT_def isTrapez_def leftP leftP_def leftRightTurn pointInRBox_def rBoxIsTrapez1 rightTurnRotate)
    apply (metis less_eq_real_def rightP rightP_def rightTurn_def signedAreaRotate topT topT_def)
    apply (metis bottomT bottomT_def leftRightTurn leftTurn_def less_eq_real_def rightP rightP_def)
    apply (metis bottomT bottomT_def isTrapez_def leftRightTurn pointInRBox_def rBoxIsTrapez1 rightTurnRotate topT topT_def)
    apply (metis bottomT bottomT_def isTrapez_def leftRightTurn pointInRBox_def rBoxIsTrapez1 rightTurnRotate topT topT_def)
    apply (metis bottomT bottomT_def isTrapez_def leftRightTurn pointInRBox_def rBoxIsTrapez1 rightTurnRotate topT topT_def)
    apply (metis bottomT bottomT_def isTrapez_def leftRightTurn pointInRBox_def rBoxIsTrapez1 rightTurnRotate topT topT_def)
    apply (metis bottomT bottomT_def isTrapez_def leftRightTurn pointInRBox_def rBoxIsTrapez1 rightTurnRotate topT topT_def)
    apply (metis bottomT bottomT_def isTrapez_def leftRightTurn pointInRBox_def rBoxIsTrapez1 rightTurnRotate topT topT_def)
    apply (metis bottomT bottomT_def isTrapez_def leftRightTurn pointInRBox_def rBoxIsTrapez1 rightTurnRotate topT topT_def)
    apply (metis bottomT bottomT_def isTrapez_def leftRightTurn pointInRBox_def rBoxIsTrapez1 rightTurnRotate topT topT_def)
    apply (metis isTrapez_def leftRightTurn pointInRBox_def rBoxIsTrapez1 rightTurnRotate topT topT_def)
    apply (metis bottomT bottomT_def isTrapez_def leftRightTurn pointInRBox_def rBoxIsTrapez1 rightTurnRotate)
   apply (case_tac "i=1")
    apply (simp add: isTrapez_def)
    apply (simp add: rBoxTrapezS_def, erule_tac x=0 in allE, simp add: pointInRBox_def, safe)
    apply (metis leftP leftP_def rightP rightP_def)
    apply (metis leftP leftP_def less_eq_real_def rightTurn_def signedAreaRotate topT topT_def)
    apply (metis areaDoublePoint bottomT bottomT_def fst_conv leftP leftP_def order_refl signedAreaRotate)*)
sorry

(*wenn a in einem Trapez, dann ist a in einem der neuem Trapeze nach dem ein Segment in trapezoidalMap aufgenommen wird*)
lemma "leftFromPoint P Q \<Longrightarrow> rBoxTrapezS [P,Q,a] R \<Longrightarrow> D =(addSegmentToTrapezoidalMap (Tip R) P Q)
  \<Longrightarrow> (\<exists> i < length (tDagList D). pointInTrapez ((tDagList D)!i) a)"
  apply (simp add: addSegmentToTrapezoidalMap_def intersectedTrapez_def sortedTrapez_def)
  apply (subgoal_tac "\<not>neighborAlongSeg R R P Q", simp, thin_tac "\<not>neighborAlongSeg R R P Q")
  apply (simp add: newDag_def newDagSimp_def)
  apply (subgoal_tac "leftP R \<noteq> P \<and> rightP R \<noteq> Q", simp add: newDagSimpQ_def newDagSimpA_def)
  apply (thin_tac "leftP R \<noteq> P \<and> rightP R \<noteq> Q")
  apply (simp add: rBoxTrapezS_def pointInRBox_def, erule_tac x=2 in allE, simp)
  apply (case_tac "xCoord a < xCoord P")
    apply (rule_tac x=0 in exI, simp add: pointInTrapez_def, auto)
    apply (auto simp add: leftFromPoint_def less_eq_real_def conflictingRigthTurns1 not_le rightTurn_def)
  apply (case_tac "xCoord Q < xCoord a")
    apply (rule_tac x=3 in exI, simp add: pointInTrapez_def, auto)
  apply (case_tac "signedArea P Q a > 0")
    apply (rule_tac x=1 in exI, simp add: pointInTrapez_def)
  apply (rule_tac x=2 in exI, simp add: pointInTrapez_def, auto)
  (*proof for Subgoals*)
  apply (simp add: rBoxTrapezS_def, erule_tac x=0 in allE, safe, simp add: pointInRBox_def)
  apply (metis leftFromPoint_def less_irrefl)
  apply (simp add: rBoxTrapezS_def, erule_tac x=1 in allE, safe,simp, (simp add: pointInRBox_def))
  apply (metis leftFromPoint_def less_irrefl)
  apply (rule_tac T=R and P=P and Q=Q in neighborTrapezSame, auto)
done
lemma "leftFromPoint P Q\<Longrightarrow> rBoxTrapezS [P,Q,a] R \<Longrightarrow> D=(addSegmentToTrapezoidalMap (Tip R) P Q)\<Longrightarrow>
  (\<exists>i<length (tDagList D). pointInTrapez((tDagList D)!i) a \<and> ((tDagList D)!i=queryTrapezoidMap D a))"
  apply (simp add: addSegmentToTrapezoidalMap_def intersectedTrapez_def sortedTrapez_def)
  apply (subgoal_tac "\<not>neighborAlongSeg R R P Q", simp)
  apply (simp add: newDag_def newDagSimp_def)
  apply (subgoal_tac "leftP R \<noteq> P \<and> rightP R \<noteq> Q",safe, simp add: newDagSimpQ_def newDagSimpA_def)
  apply (simp add: rBoxTrapezS_def pointInRBox_def, erule_tac x=2 in allE)
  apply (case_tac "xCoord a < xCoord P")
    apply (rule_tac x=0 in exI, simp add: pointInTrapez_def)
    apply (metis areaContra leftFromPoint_def not_less not_less_iff_gr_or_eq rightTurn_def, simp)
  apply (case_tac "xCoord Q < xCoord a")
    apply (rule_tac x=3 in exI, simp add: pointInTrapez_def)
  apply (case_tac "signedArea P Q a > 0")
    apply (rule_tac x=1 in exI, simp)
    apply (safe, bestsimp)
    apply (simp add: pointInTrapez_def del:signedAreaRotate signedAreaRotate2)
    apply (simp add: newDagSimpQ_def newDagSimpA_def rBoxTrapezS_def del:signedAreaRotate signedAreaRotate2)
    apply (erule_tac x=2 in allE, simp add: pointInRBox_def del:signedAreaRotate signedAreaRotate2)
  apply (rule_tac x=2 in exI, simp add: pointInTrapez_def, auto)
  (*proof for Subgoals*)
  apply (simp add: rBoxTrapezS_def, erule_tac x=0 in allE, safe, simp add: pointInRBox_def)
  apply (metis leftFromPoint_def less_irrefl)
  apply (simp add: rBoxTrapezS_def, erule_tac x=1 in allE, safe,simp, (simp add: pointInRBox_def))
  apply (metis leftFromPoint_def less_irrefl)
  apply (rule_tac T=R and P=P and Q=Q in neighborTrapezSame, auto)
oops


(*****Add Polygon to trapezoidal-map*)
(*Input: List of line segments(one Polygon) forming a planar subdivision.
Output:  A trapezoid map M in associated search structure tDag.*)
fun addSegmentsToTrapezoidalMap :: "tDag \<Rightarrow> point2d list \<Rightarrow> tDag" where
  "addSegmentsToTrapezoidalMap D [] = D"
  | "addSegmentsToTrapezoidalMap D [q] = D"
  | "addSegmentsToTrapezoidalMap D (p#q#xs) =
  addSegmentsToTrapezoidalMap (addSegmentToTrapezoidalMap D (leftPSegment p q) (rightPSegment p q)) (q#xs)"

(*füge Segment in tDag ein, wenn tDag \<noteq> rBox*)
lemma addSegmentToDag1: "uniqueXCoord (P#Q#L) \<Longrightarrow> intersectionFreePList L \<Longrightarrow>
  rBoxTrapezS L R \<Longrightarrow> dag = addPolygonToTrapezoidalMap (Tip R) L \<Longrightarrow>
  leftFromPoint P Q \<Longrightarrow> \<not>lineCyclePathInters L P Q \<Longrightarrow> rBoxTrapezS [P,Q,a] R \<Longrightarrow>
  D = addSegmentToTrapezoidalMap dag P Q \<Longrightarrow>
  \<exists> i < length (tDagList D). pointInTrapez ((tDagList D)!i) a \<and> ((tDagList D)!i = queryTrapezoidMap D a)"
oops

(*Input: rBox, tDag(start with rBox) and a polygon forming a planar subdivision.
Output:  A trapezoid map M in associated search structure tDag.*)
definition simpTrapezoidalMap :: "trapez \<Rightarrow> point2d list \<Rightarrow> tDag" where
  "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> uniqueXCoord L \<Longrightarrow> rBoxTrapezS L R \<Longrightarrow>
  simpTrapezoidalMap R P  \<equiv> addSegmentsToTrapezoidalMap (Tip R) P"

(*jedes a was in rBox ist, ist auch nach dem Hinzufügen von einem Polygon in einem der Trapeze zu finden*)
lemma addPolygonToRBox: "uniqueXCoord L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow>
  rBoxTrapezS L R \<Longrightarrow> D = simpTrapezoidalMap R P \<Longrightarrow> rBoxTrapezS [a] R \<Longrightarrow>
  \<exists> i < length (tDagList D). pointInTrapez ((tDagList D)!i) a \<and> ((tDagList D)!i = queryTrapezoidMap D a)"
oops


(*zeige das keine der segmente von trapezodialMap das polygon innerhalb von rBox schneidet*)
(*untere und obere Strecken von trapezen, sind segmente von den polygonen*)
lemma "pointList L \<Longrightarrow> P = cyclePath L \<Longrightarrow> polygon P \<Longrightarrow> uniqueXCoord L \<Longrightarrow> rBoxTrapezS L R \<Longrightarrow>
  TL = tDagList (simpTrapezoidalMap R P) \<Longrightarrow> i < length TL \<longrightarrow>
    segInPointList P (bottomT(TL!i)) \<and> segInPointList P (topT(TL!i))"
  apply (auto simp add: segInPointLists_def)
oops


(*add Polygons to trapezoidal-Map*)
(*****Add Polygon to trapezoidal-map*)
(*Input: List of line segments(one Polygon) forming a planar subdivision.
Output:  A trapezoid map M in associated search structure tDag.*)
fun addPolygonsToTrapezoidalMap :: "tDag \<Rightarrow> (point2d list) list \<Rightarrow> tDag" where
  "addPolygonsToTrapezoidalMap D [] = D"
  | "addPolygonsToTrapezoidalMap D (P#PL) =
    addPolygonsToTrapezoidalMap (addSegmentsToTrapezoidalMap D (cyclePath P)) PL"

(*Input: rBox, tDag(start with rBox) and a polygon forming a planar subdivision.
Output:  A trapezoid map M in associated search structure tDag.*)
definition buildTrapezoidalMap :: "trapez \<Rightarrow> (point2d list) list \<Rightarrow> tDag" where
  "pointLists PL \<Longrightarrow> polygonList PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow> rBoxTrapezS (concat PL) R \<Longrightarrow>
  \<not>cyclePathsIntersect PL \<Longrightarrow> buildTrapezoidalMap R PL \<equiv> addPolygonsToTrapezoidalMap (Tip R) PL"

(*jedes a was in rBox ist, ist auch nach dem Hinzufügen von mehreren Polygonen in einem der Trapeze zu finden*)
lemma buildTrapezoidalMap : "uniqueXCoord ((concat PL)) \<Longrightarrow> polygonList PL \<Longrightarrow> cyclePathsIntersect PL \<Longrightarrow>
  rBoxTrapezS ((concat PL)) R \<Longrightarrow> D = buildTrapezoidalMap R PL \<Longrightarrow> rBoxTrapezS [a] R \<Longrightarrow>
  (\<exists> i < length (tDagList D). pointInTrapez ((tDagList D)!i) a \<and> ((tDagList D)!i = queryTrapezoidMap D a))"
oops





(*alte Definition*)

(*gib den nächsten Nachbarn von einem Trapez folgend der Strecke PQ  aus der Trapez-Liste
Input: tDag, tDagList geordnet nach der x-Coordinate von leftP, Strecke PQ
Output: nächster trapez-Nachbar, wenn man PQ folgt*)
(*es muss ein Nachbar geben! kein Nachbar wird ausgelassen!*)
fun nextTrapez :: "trapez list \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez" where
  "nextTrapez (Ts#Tm) T P Q = (if(neighborAlongSeg T Ts P Q) then(Ts) else(nextTrapez Tm T P Q))"
(*beweise das das nächste Trapez rechts von dem linkem Trapez*)
lemma "leftFromPoint P Q \<Longrightarrow> Tl = queryTrapezoidMap D P \<Longrightarrow> Tl \<noteq> Tr \<Longrightarrow> Tr = queryTrapezoidMap D R \<Longrightarrow> 
  leftFromPoint (leftP Tl) (leftP (nextTrapez (tDagList D) Tl P Q))"
  apply (subgoal_tac "tDagList D \<noteq> []")
  apply (case_tac "((tDagList D), Tl, P, Q)" rule: nextTrapez.cases)
  apply (auto)
oops
(*es gibt ein T in D sodass rightP T > Q*)
lemma "length (tDagList D) > 1\<Longrightarrow>
  Ts = nextTrapez (tDagList D) T P Q \<Longrightarrow> leftFromPoint (rightP T) (rightP Ts)"
  apply (cases "tDagList D", simp)
  apply (auto simp add: neighborAlongSeg_def)
oops


(*The termination argument for followS is based on the fact that the difference
between "xCoord (rightP T)" and  "xCoord Q"  gets smaller in every step*) 
function followS :: "tDag \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> trapez list" where
  "followS D T P Q = (if(leftFromPoint (rightP T) Q)
  then(followS D (nextTrapez (tDagList D) T P Q) P Q)
  else ([]))"
by pat_completeness auto
termination followS 
 apply (auto)(*beweise das das nächste Trapez rechts von dem linkem Trapez
  bzw. dass der Abstand zwischen rightP T und Q immer kleiner wird*)
(*dafür müssen aber entweder in tDag noch annahmen stecken oder es muss eine condition für followS geben*)
(*functions with conditional patterns are not supported by the code generator.*)
sorry

(*
(*Input: tDag(start with rBox) and List of polygons forming a planar subdivision.
Output:  A trapezoid map M in associated search structure tDag.*)
fun buildTrapezoidalMap :: "tDag \<Rightarrow> (point2d list) list \<Rightarrow> tDag" where
  "buildTrapezoidalMap D [] = D"
  |"buildTrapezoidalMap D (P#Pl) = buildTrapezoidalMap (polygonExtendTrapezoidalMap D P) Pl"*)

end
