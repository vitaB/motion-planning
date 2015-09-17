theory trapez
imports polygon
begin

(*identifiers for Trapez-parts*)
definition topT1 :: "(point2d\<times>point2d)\<times>(point2d\<times>point2d)\<times>point2d\<times>point2d \<Rightarrow> (point2d\<times>point2d)"
  where  "topT1 T \<equiv> fst T"
definition bottomT1 :: "(point2d\<times>point2d)\<times>(point2d\<times>point2d)\<times>point2d\<times>point2d \<Rightarrow> (point2d\<times>point2d)"
  where "bottomT1 T \<equiv> fst(snd T)"
definition leftP1 :: "(point2d\<times>point2d)\<times>(point2d\<times>point2d)\<times>point2d\<times>point2d \<Rightarrow> point2d" where
  "leftP1 T \<equiv> fst(snd(snd T))"
definition rightP1 :: "(point2d\<times>point2d)\<times>(point2d\<times>point2d)\<times>point2d\<times>point2d \<Rightarrow> point2d" where
  "rightP1 T \<equiv> snd(snd(snd T))"

definition trapezPointsXOrder ::"(point2d\<times>point2d)\<times>(point2d\<times>point2d)\<times>point2d\<times>point2d \<Rightarrow> bool"where
  "trapezPointsXOrder p \<equiv> leftFromPoint (leftP1 p) (rightP1 p) (*e links von f*)
  \<and> leftFromPoint (fst(topT1 p)) (snd(topT1 p)) (*a ist links von b*)
  \<and> leftFromPoint (fst(bottomT1 p)) (snd(bottomT1 p)) (*c ist links von d*) 
  \<and> xCoord (leftP1 p) \<ge> xCoord (fst(topT1 p)) \<and> xCoord (leftP1 p) \<ge> xCoord (fst(bottomT1 p)) (*e \<ge> a \<and> c*)
  \<and> xCoord (rightP1 p) \<le> xCoord (snd(topT1 p)) \<and> xCoord (rightP1 p) \<le> xCoord (snd(bottomT1 p))(*f \<le> b \<and> d*)"

(*e < b \<and> d*)
lemma trapezHasOrderetPoints1: "trapezPointsXOrder p \<Longrightarrow>
  leftFromPoint (leftP1 p)(snd(topT1 p)) \<and> leftFromPoint (leftP1 p) (snd(bottomT1 p))"
  apply (simp add: leftFromPoint_def)
using leftFromPoint_def Orderings.xt1(8) trapezPointsXOrder_def by blast
(*f > a \<and> c*)
lemma trapezHasOrderetPoints2: "trapezPointsXOrder p \<Longrightarrow>
  leftFromPoint (fst(topT1 p)) (rightP1 p) \<and> leftFromPoint(fst(bottomT1 p)) (rightP1 p)"
  using leftFromPoint_def trapezPointsXOrder_def by auto
(*a < d*)
lemma trapezHasOrderetPoints3:"trapezPointsXOrder T \<Longrightarrow>leftFromPoint (fst(topT1 T)) (snd(bottomT1 T))"
  by (auto simp add: trapezPointsXOrder_def leftFromPoint_def)
(*b > c*)
lemma trapezHasOrderetPoints4:"trapezPointsXOrder T \<Longrightarrow>leftFromPoint (fst(bottomT1 T)) (snd(topT1 T))"
  by (auto simp add: trapezPointsXOrder_def leftFromPoint_def)

(*e ist zwischen ab und cd oder e=a oder e=c*)
definition trapezQuad:: "(point2d\<times>point2d)\<times>(point2d\<times>point2d)\<times>point2d\<times>point2d \<Rightarrow> bool" where
  "trapezQuad p \<equiv>
  rightTurn (fst(topT1 p)) (snd(topT1 p)) (leftP1 p) (*e ist zwischen ab und cd*)
    \<and> leftTurn (fst(bottomT1 p)) (snd(bottomT1 p)) (leftP1 p) 
    \<and> rightTurn (fst(topT1 p)) (snd(topT1 p)) (rightP1 p)(* und f ist zwischen ab und cd*)
    \<and> leftTurn (fst(bottomT1 p)) (snd(bottomT1 p)) (rightP1 p)
    \<and> fst(topT1 p) \<noteq> fst(bottomT1 p) \<and> snd(topT1 p) \<noteq> snd(bottomT1 p) (*a\<noteq>c \<and> b\<noteq>d*)
    \<and> rightTurn (fst(topT1 p)) (snd(topT1 p)) (fst(bottomT1 p))(*a und b über c und d*)
    \<and> rightTurn (fst(topT1 p)) (snd(topT1 p)) (snd(bottomT1 p))"

lemma trapezTriangleVertex1: "trapezQuad p \<Longrightarrow>
  leftTurn (fst(bottomT1 p)) (snd(bottomT1 p)) (snd(topT1 p))
  \<and> leftTurn (fst(bottomT1 p)) (snd(bottomT1 p)) (fst(topT1 p))"
  apply (auto simp add: trapezQuad_def)
oops

definition trapezTriangle :: "(point2d\<times>point2d)\<times>(point2d\<times>point2d)\<times>point2d\<times>point2d \<Rightarrow> bool" where
   "trapezTriangle p \<equiv> (leftTurn (fst(bottomT1 p)) (snd(bottomT1 p)) (fst(topT1 p)) (*a ist über cd*)
    \<and> leftTurn (fst(bottomT1 p)) (snd(bottomT1 p)) (leftP1 p) (*e ist über cd*)
    \<and> rightTurn (fst(topT1 p)) (snd(topT1 p)) (leftP1 p) (*e ist unter a b*)
    \<and> snd(bottomT1 p) = snd(topT1 p) \<and> snd(bottomT1 p) = rightP1 p  (*und d=b=f*)
   )\<or>
   (fst(topT1 p) = fst(bottomT1 p) \<and> fst(bottomT1 p) = leftP1 p (*a=c=e*)
    \<and> leftTurn (fst(bottomT1 p)) (snd(bottomT1 p)) (snd(topT1 p)) (*b über c d*)
    \<and> rightTurn (fst(topT1 p)) (snd(topT1 p)) (rightP1 p) (*f ist unter a b*)
    \<and> leftTurn (fst(bottomT1 p)) (snd(bottomT1 p)) (rightP1 p))" (*f ist über c d*)

lemma trapezTriangleVertex: "trapezTriangle p \<Longrightarrow> 
  (leftTurn (fst(bottomT1 p)) (snd(bottomT1 p)) (snd(topT1 p)) \<and> fst(topT1 p) = fst(bottomT1 p))
  \<or> (leftTurn (fst(bottomT1 p)) (snd(bottomT1 p)) (fst(topT1 p)) \<and> snd(topT1 p) = snd(bottomT1 p))"
by (auto simp add: trapezTriangle_def)

(*Definition für Trapez ((a,b),(c,d),e,f)) top: (a,b), bottom:(c,d), leftP:e, rightP: f
  a=fst(fst p), b = snd(fst p), c=fst(fst(snd p)), d=snd(fst(snd p)), e=fst(snd(snd p)), f=snd(snd(snd p))*)
definition "isTrapez T \<equiv> trapezPointsXOrder T \<and> (trapezQuad T \<or> trapezTriangle T)"

(*linke Ecke ist links von der rechten Ecke*)
lemma leftPRigthFromRightP [simp] : "isTrapez T \<Longrightarrow> leftFromPoint (leftP1 T) (rightP1 T)"
  by (simp add: isTrapez_def trapezPointsXOrder_def)
(*Linke Ecken sind rechts von den rechten Ecken*)
lemma trapezNeighbour1 : "isTrapez T \<Longrightarrow> isTrapez Ts \<Longrightarrow> rightP1 T = leftP1 Ts \<Longrightarrow>
  leftFromPoint (rightP1 T) (rightP1 Ts)"
  by (cases T, simp)
lemma trapezNeighbour2 : "isTrapez T \<Longrightarrow> isTrapez Ts \<Longrightarrow> rightP1 T = leftP1 Ts \<Longrightarrow>
  leftFromPoint (leftP1 T) (leftP1 Ts)"
  by (metis leftPRigthFromRightP)



typedef trapez = "{p::((point2d*point2d)*(point2d*point2d)*point2d*point2d). isTrapez p}"
  sorry
lemma isTrapez1 [simp]: "Rep_trapez T = T' \<longleftrightarrow> 
  (fst(Rep_trapez T) = fst(T') \<and> fst(snd(Rep_trapez T)) = fst(snd(T'))
  \<and> fst(snd(snd(Rep_trapez T))) = fst(snd(snd(T'))) 
  \<and> snd(snd(snd(Rep_trapez T))) = snd(snd(snd(T'))))"
  by (meson prod_eqI)


definition trapezNotEq :: "trapez \<Rightarrow> trapez \<Rightarrow> bool" where "trapezNotEq A B \<equiv> A \<noteq> B"
lemma [simp]: "isTrapez (a, c, e, f) \<Longrightarrow> fst (Rep_trapez (Abs_trapez (a, c, e, f))) = a"
  by (simp add: Abs_trapez_inverse) 
lemma [simp]:"isTrapez (a, c, e, f) \<Longrightarrow> fst(snd (Rep_trapez (Abs_trapez (a, c, e, f)))) = c"
  by (simp add: Abs_trapez_inverse) 
lemma [simp]:"isTrapez (a, c, e, f) \<Longrightarrow> fst(snd(snd (Rep_trapez (Abs_trapez (a, c, e, f))))) = e"
  by (simp add: Abs_trapez_inverse) 
lemma [simp]:"isTrapez (a, c, e, f) \<Longrightarrow> snd(snd(snd (Rep_trapez (Abs_trapez (a, c, e, f))))) = f"
  by (simp add: Abs_trapez_inverse) 

(*identifiers for Trapez-parts*)
definition topT :: "trapez \<Rightarrow> (point2d\<times>point2d)" where  "topT T \<equiv> fst(Rep_trapez T)"
definition bottomT :: "trapez \<Rightarrow> (point2d\<times>point2d)" where "bottomT T \<equiv> fst(snd(Rep_trapez T))"
definition leftP :: "trapez \<Rightarrow> point2d" where "leftP T \<equiv> fst(snd(snd(Rep_trapez T)))"
definition rightP :: "trapez \<Rightarrow> point2d" where "rightP T \<equiv> snd(snd(snd(Rep_trapez T)))"

(*Lemmas zum reduzieren von trapez Termen*)
lemma topT [simp]: "isTrapez (a, b, e, f) \<Longrightarrow> topT (Abs_trapez (a, b, e, f)) = a"
  by (simp add: topT_def)
lemma bottomT [simp]: "isTrapez (a, b, e, f) \<Longrightarrow> bottomT (Abs_trapez (a , b, e, f)) = b"
  by (auto simp add: bottomT_def)
lemma leftP [simp]: "isTrapez (a, b, e, f) \<Longrightarrow> leftP (Abs_trapez (a, b, e, f)) = e"
  by (auto simp add: leftP_def)
lemma rightP [simp]: "isTrapez (a, b, e, f) \<Longrightarrow> rightP (Abs_trapez (a, b, e, f)) = f"
  by (auto simp add: rightP_def)
lemma isTrapezTopT[simp]: "isTrapez T \<Longrightarrow> topT1 T = topT (Abs_trapez T)"
  by (simp add: Abs_trapez_inverse topT1_def topT_def)
lemma isTrapezBottomT[simp]: "isTrapez T \<Longrightarrow> bottomT1 T = bottomT (Abs_trapez T)"
  by (simp add: Abs_trapez_inverse bottomT1_def bottomT_def)
lemma isTrapezLeftP[simp]: "isTrapez T \<Longrightarrow> leftP1 T = leftP (Abs_trapez T)"
  by (simp add: Abs_trapez_inverse leftP1_def leftP_def)
lemma isTrapezRightP[simp]: "isTrapez T \<Longrightarrow> rightP1 T = rightP (Abs_trapez T)"
  by (simp add: Abs_trapez_inverse rightP1_def rightP_def)


(*e < b \<and> d*)
lemma trapezHasOrderetPoints5: "leftFromPoint (leftP p)(snd(topT p))
  \<and> leftFromPoint (leftP p) (snd(bottomT p))"
  apply (cases p, simp add: leftFromPoint_def)
by (metis isTrapezTopT isTrapezBottomT isTrapezLeftP isTrapez_def leftFromPoint_def
  trapezHasOrderetPoints1)
(*f > a \<and> c*)
lemma trapezHasOrderetPoints6: "leftFromPoint (fst(topT p)) (rightP p)
  \<and> leftFromPoint(fst(bottomT p)) (rightP p)"
by (metis Abs_trapez_cases Abs_trapez_inverse isTrapezBottomT isTrapezRightP isTrapez_def
  mem_Collect_eq topT1_def topT_def trapezHasOrderetPoints2)
(*a < d*)
lemma trapezHasOrderetPoints7:"leftFromPoint (fst(topT T)) (snd(bottomT T))"
by (metis Abs_trapez_cases Abs_trapez_inverse isTrapezBottomT isTrapez_def mem_Collect_eq
  topT1_def topT_def trapezHasOrderetPoints3)
(*b > c*)
lemma trapezHasOrderetPoints8:"leftFromPoint (fst(bottomT T)) (snd(topT T))"
  by (metis Abs_trapez_cases Abs_trapez_inverse isTrapezBottomT isTrapez_def mem_Collect_eq
  topT1_def topT_def trapezHasOrderetPoints4)



lemma trapezTriangleVertex4: "
  leftTurn (fst(bottomT p)) (snd(bottomT p)) (snd(topT p))
  \<or> leftTurn (fst(bottomT p)) (snd(bottomT p)) (fst(topT p))"
  apply (case_tac p, simp add: isTrapez_def, erule conjE, erule disjE) defer
  apply (metis isTrapezBottomT isTrapezTopT isTrapez_def leftRightTurn rightTurnRotate2
    trapezTriangleVertex)
  apply (rule)
oops


(*linke Ecke ist links von der rechten Ecke*)
lemma leftPRigthFromRightP1 [simp] : "leftFromPoint (leftP T) (rightP T)"
  by (metis Rep_trapez Rep_trapez_inverse isTrapezLeftP isTrapezRightP leftPRigthFromRightP
    mem_Collect_eq)
(*Linke Ecken sind rechts von den rechten Ecken*)
lemma trapezNeighbour3 : "rightP T = leftP Ts \<Longrightarrow>
  leftFromPoint (rightP T) (rightP Ts)"
  by (cases T, simp)
lemma trapezNeighbour4 : "rightP T = leftP Ts \<Longrightarrow>
  leftFromPoint (leftP T) (leftP Ts)"
  by (metis leftPRigthFromRightP1)

(*jeder Punkt der auf der xCoordinate von rightP steht und von topT und bottomT eingegrenzt wird*)
definition pointOnLeftT :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where
  "pointOnLeftT T p \<equiv> rightTurn (fst(topT T)) (snd(topT T)) p
    \<and> leftTurn (fst(bottomT T)) (snd(bottomT T)) p \<and> xCoord (leftP T) = xCoord p"
definition pointOnRightT :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where
  "pointOnRightT T p \<equiv> rightTurn (fst(topT T)) (snd(topT T)) p
    \<and> leftTurn (fst(bottomT T)) (snd(bottomT T)) p \<and> xCoord (rightP T) = xCoord p"
lemma pointNotOnLeftRightT[dest]: "pointOnLeftT T p \<Longrightarrow> pointOnRightT T p \<Longrightarrow> False"
  apply (simp add: pointOnLeftT_def pointOnRightT_def isTrapez_def trapezPointsXOrder_def)
by (metis leftFromPoint_def leftPRigthFromRightP1 less_irrefl)


(*topT und bottomT sind segmente*)
lemma topTSegment [simp]: "segment (fst(topT T)) (snd(topT T))"
  apply (cases T, subgoal_tac "xCoord (fst(topT T)) \<noteq> xCoord (snd(topT T))")
  apply (simp add: isTrapez_def)
by (metis Abs_trapez_inverse isTrapez_def leftFromPoint_def mem_Collect_eq not_less rightP1_def
  rightP_def topT1_def topT_def trapezHasOrderetPoints6 trapezPointsXOrder_def)
lemma bottomTSegment [simp]: "segment (fst(bottomT T)) (snd(bottomT T))"
  apply (cases T, subgoal_tac "xCoord (fst(bottomT T)) \<noteq> xCoord (snd(bottomT T))")
  apply (simp add: isTrapez_def)
by (metis Abs_trapez_inverse bottomT1_def bottomT_def isTrapez_def leftFromPoint_def
  mem_Collect_eq not_le trapezHasOrderetPoints2 trapezPointsXOrder_def)
lemma foo: "c \<noteq> d \<Longrightarrow> leftFromPoint c d \<Longrightarrow> leftFromPoint a b \<Longrightarrow> rightTurn a b c \<Longrightarrow>
  rightTurn a b d \<Longrightarrow> leftFromPoint a d \<Longrightarrow> leftFromPoint c b\<Longrightarrow> leftTurn c d a \<or> leftTurn c d  b"
  apply (case_tac "lineSeparate a b c d") using lineSeparate_def apply auto[1]
  apply (case_tac "lineSeparate c d a b") using lineSeparate_def apply auto[1]
  apply (subgoal_tac "\<not>collinear c b d")
  apply (case_tac "collinear a c d", rule disjI2)
oops
  
(*Beweise über die Positionen der Ecken vom Trapez*)
(*engegengesetzte Ecken des Trapezes sind von einander ungleich*)
lemma trapezVertex: "snd(topT p) \<noteq> fst(bottomT p) \<and> snd(bottomT p) \<noteq> fst(topT p)"
  by (metis leftFromPointDest trapezHasOrderetPoints7 trapezHasOrderetPoints8)
(*mind. einer der Ecken von topT ist über bottomT*)
lemma topAboveBottom [intro] :"
  leftTurn (fst (bottomT T)) (snd (bottomT T)) (fst (topT T)) 
  \<or> leftTurn (fst (bottomT T)) (snd (bottomT T)) (snd (topT T))"
  apply (auto simp add: isTrapez_def)
oops
(*leftP ist über bottom T oder ist die linke Ecke von bottomT*)
lemma leftPPos [intro] : "leftTurn (fst(bottomT T)) (snd(bottomT T)) (leftP T) \<or> (fst(bottomT T) = leftP T)"nitpick[timeout=400]
  apply (simp add: leftP_def bottomT_def del: leftRightTurn leftTurnRotate leftTurnRotate2,
    cases T, simp del: leftRightTurn leftTurnRotate leftTurnRotate2)
by (metis bottomT_def isTrapezBottomT isTrapezLeftP isTrapez_def leftP_def trapezQuad_def
  trapezTriangle_def)

lemma rightPPos [intro] : "rightTurn (fst(topT T)) (snd(topT T)) (rightP T)
  \<or> (snd(topT T) = rightP T)"
  apply (simp add: leftP_def bottomT_def del: leftRightTurn leftTurnRotate leftTurnRotate2,
   cases T, simp del: leftRightTurn leftTurnRotate leftTurnRotate2)
by(metis isTrapezRightP isTrapezTopT isTrapez_def rightTurnRotate trapezQuad_def trapezTriangle_def)


(*Trapez Equiv.*)
lemma trapezSameCoord[simp]: "isTrapez ((a,b),(c,d),e,f) \<Longrightarrow> isTrapez ((a',b'),(c',d'),e',f') \<Longrightarrow>
  (Abs_trapez ((a,b),(c,d),e,f) = Abs_trapez ((a',b'),(c',d'),e',f'))
  \<longleftrightarrow> (a=a'\<and> b=b' \<and> c=c' \<and> d=d' \<and> e=e' \<and> f=f')"
using Abs_trapez_inverse by fastforce

lemma trapezSameCoord1[simp]: "isTrapez (a,c,e,f) \<Longrightarrow> isTrapez (a',c',e',f') \<Longrightarrow>
(Abs_trapez (a,c,e,f) = Abs_trapez (a',c',e',f')) \<longleftrightarrow> (a=a' \<and> c=c'\<and> e=e' \<and> f=f')"
using Abs_trapez_inverse by fastforce


definition neighbor :: "trapez \<Rightarrow> trapez \<Rightarrow> bool" where
  "neighbor T Tr \<equiv> rightP T = leftP Tr \<and> (topT T = topT Tr \<or> bottomT T = bottomT Tr)"
(*zwei Trapeze sind benachbart entland der Strecke PQ, wenn :
  - die linke Ecke eines Trapezes gleich der rechten Ecke des anderen Trapezes
  - topT gleich sind, falls PQ über rightPT bzw. bottomT gleich sind, falls PQ unter rightP.*)
definition neighborAlongSeg :: "trapez \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "leftFromPoint P Q \<Longrightarrow> neighborAlongSeg T Ts P Q \<equiv> rightP T = leftP Ts \<and>
  ((rightTurn P Q (rightP T) \<and> topT T = topT Ts)
    \<or> (leftTurn P Q (rightP T) \<and> bottomT T = bottomT Ts))"
lemma neighborTrapezSame[dest]: "leftFromPoint P Q \<Longrightarrow> neighborAlongSeg T T P Q \<Longrightarrow> False"
by (auto simp add: neighborAlongSeg_def,(metis leftFromPoint_def less_irrefl trapezNeighbour3)+)


(*ein Punkt P ist im Trapez T, wenn es auf den Kanten liegt, oder innerhalb des T*)
(*stimmt, weil von Vertikalen eingegrenzt*)
definition pointInTrapez :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where 
  "pointInTrapez T P \<equiv> xCoord P \<le> xCoord (rightP T) \<and> xCoord P \<ge> xCoord (leftP T)
  \<and> signedArea (fst(bottomT T)) (snd(bottomT T)) P \<ge> 0 \<and> signedArea (fst(topT T)) (snd(topT T)) P \<le> 0"
(*Punkt ist im Trapez, aber nicht auf den Kanten*)
definition pointInTrapezInner :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where 
  "pointInTrapezInner T P \<equiv> xCoord P \<le> xCoord (rightP T) \<and> xCoord P \<ge> xCoord (leftP T)
  \<and> leftTurn (fst(bottomT T)) (snd(bottomT T)) P  \<and> rightTurn (fst(topT T)) (snd(topT T)) P
  \<and> P \<noteq> rightP T \<and> P \<noteq> leftP T"
lemma InnerToPointInTrapez[simp]: "pointInTrapezInner T P \<Longrightarrow> pointInTrapez T P"
  apply (auto simp add: pointInTrapez_def pointInTrapezInner_def)
  using rightTurn_def apply auto[1] using rightTurn_def apply auto[1]
done

(*definition trapezSegmentCrossing :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "trapezSegmentCrossing T P Q \<equiv> crossing (fst (topT T)) (snd (topT T)) P Q
    \<or> crossing (fst (bottomT T)) (snd (bottomT T)) P Q"*)




(*definition isTrapezoidal :: "trapez \<times> (trapez \<times> trapez) \<times> (trapez \<times> trapez) \<Rightarrow> bool" where
  "isTrapezoidal p \<equiv> neighbor (fst(fst(snd p))) (fst p) \<and> neighbor (snd(fst(snd p))) (fst p)
  \<and> neighbor (fst p) (fst(snd(snd p))) \<and> neighbor (fst p) (snd(snd(snd p)))
  \<and> isTrapez (fst p) \<and> isTrapez (fst(fst(snd p))) \<and> isTrapez (snd(fst(snd p)))
  \<and> isTrapez (fst(snd(snd p))) \<and> isTrapez (snd(snd(snd p)))"
typedef trapezoidal = "{p::(trapez*(trapez*trapez)*(trapez*trapez)). isTrapezoidal p}"
  sorry

definition getTrapez :: "trapezoidal \<Rightarrow> trapez" where
  "getTrapez TM \<equiv> fst(Rep_trapezoidal TM)"
lemma getTrapez[simp]: 
  "isTrapezoidal (a,(b,c),(d,e)) \<Longrightarrow> getTrapez (Abs_trapezoidal (a,(b,c),(d,e))) = a"
  by (simp add: Abs_trapezoidal_inverse getTrapez_def)
definition upRNeighb :: "trapezoidal \<Rightarrow> trapez" where
  "upRNeighb TM \<equiv> fst(snd(snd(Rep_trapezoidal TM)))"
lemma upRNeighb[simp]: 
  "isTrapezoidal (a,(b,c),(d,e)) \<Longrightarrow> upRNeighb (Abs_trapezoidal (a,(b,c),(d,e))) = d"
  by (simp add: Abs_trapezoidal_inverse upRNeighb_def)
definition btRNeighb :: "trapezoidal \<Rightarrow> trapez" where
  "btRNeighb TM \<equiv> snd(snd(snd(Rep_trapezoidal TM)))"
lemma btRNeighb[simp]:
  "isTrapezoidal (a,(b,c),(d,e)) \<Longrightarrow> btRNeighb (Abs_trapezoidal (a,(b,c),(d,e))) = e"
  by (simp add: Abs_trapezoidal_inverse btRNeighb_def)
definition upLNeighb :: "trapezoidal \<Rightarrow> trapez" where
  "upLNeighb TM \<equiv> fst(fst(snd(Rep_trapezoidal TM)))"
lemma upLNeighb[simp]: 
  "isTrapezoidal (a,(b,c),(d,e)) \<Longrightarrow> upLNeighb (Abs_trapezoidal (a,(b,c),(d,e))) = b"
  by (simp add: Abs_trapezoidal_inverse upLNeighb_def)
definition btLNeighb :: "trapezoidal \<Rightarrow> trapez" where
  "btLNeighb TM \<equiv> snd(fst(snd(Rep_trapezoidal TM)))"
lemma btLNeighb[simp]:
  "isTrapezoidal (a,(b,c),(d,e)) \<Longrightarrow> btLNeighb (Abs_trapezoidal (a,(b,c),(d,e))) = c"
  by (simp add: Abs_trapezoidal_inverse btLNeighb_def)

lemma trapezoidalVertex[simp] : "leftFromPoint (leftP (getTrapez TM)) (leftP (upRNeighb TM))"
  by (metis Rep_trapezoidal getTrapez_def isTrapezoidal_def leftPRigthFromRightP mem_Collect_eq
    neighbor_def upRNeighb_def)
lemma trapezoidalVertex1[simp] : "leftFromPoint (leftP (getTrapez TM)) (leftP (btRNeighb TM))"
  by (metis Rep_trapezoidal getTrapez_def isTrapezoidal_def leftPRigthFromRightP mem_Collect_eq
    neighbor_def btRNeighb_def)*)
  

end
