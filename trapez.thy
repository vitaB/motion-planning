theory trapez
imports polygon
begin

typedef trapez = "{p::((point2d*point2d)*(point2d*point2d)*point2d*point2d). True}" by (auto)
lemma [simp]: "fst (Rep_trapez (Abs_trapez (a, c, e, f))) = a" by (simp add: Abs_trapez_inverse) 
lemma [simp]:"fst(snd (Rep_trapez (Abs_trapez (a, c, e, f)))) = c" by (simp add: Abs_trapez_inverse) 
lemma [simp]:"fst(snd(snd (Rep_trapez (Abs_trapez (a, c, e, f))))) = e"
  by (simp add: Abs_trapez_inverse) 
lemma [simp]:"snd(snd(snd (Rep_trapez (Abs_trapez (a, c, e, f))))) = f"
  by (simp add: Abs_trapez_inverse) 
(*Trapez Equiv.*)
definition trapezNotEq :: "trapez \<Rightarrow> trapez \<Rightarrow> bool" where "trapezNotEq A B \<equiv> A \<noteq> B"
lemma trapezSameCoord[simp]: "(Abs_trapez ((a,b),(c,d),e,f) = Abs_trapez ((a',b'),(c',d'),e',f'))
  \<longleftrightarrow> (a=a'\<and> b=b' \<and> c=c' \<and> d=d' \<and> e=e' \<and> f=f')"
  by (metis Abs_trapez_inverse fst_conv mem_Collect_eq prod.inject)
lemma trapezSameCoord1[simp]: "(Abs_trapez (a,c,e,f) = Abs_trapez (a',c',e',f')) \<longleftrightarrow>
  (a=a' \<and> c=c'\<and> e=e' \<and> f=f')"
  by (metis Abs_trapez_inverse fst_conv mem_Collect_eq prod.inject)

(*identifiers for Trapez-parts*)
definition topT :: "trapez \<Rightarrow> (point2d\<times>point2d)" where  "topT T \<equiv> fst(Rep_trapez T)"
definition bottomT :: "trapez \<Rightarrow> (point2d\<times>point2d)" where "bottomT T \<equiv> fst(snd(Rep_trapez T))"
definition leftP :: "trapez \<Rightarrow> point2d" where "leftP T \<equiv> fst(snd(snd(Rep_trapez T)))"
definition rightP :: "trapez \<Rightarrow> point2d" where "rightP T \<equiv> snd(snd(snd(Rep_trapez T)))"

(*Lemmas zum reduzieren von trapez Termen*)
lemma topT [simp]: "topT (Abs_trapez (a, b, e, f)) = a" by (simp add: Abs_trapez_inverse topT_def)
lemma bottomT [simp]: "bottomT (Abs_trapez (a , b, e, f)) = b"
  by (auto simp add: Abs_trapez_inverse bottomT_def)
lemma leftP [simp]: "leftP (Abs_trapez (a, b, e, f)) = e" 
  by (auto simp add: Abs_trapez_inverse leftP_def)
lemma rightP [simp]: " rightP (Abs_trapez (a, b, e, f)) = f"
  by (auto simp add: Abs_trapez_inverse rightP_def)

(*Anordnung der Trapez-Punkte auf der x-Koordinate*)
definition trapezPointsXOrder ::"trapez \<Rightarrow> bool"where
  "trapezPointsXOrder p \<equiv> leftFrom (leftP p) (rightP p) (*e links von f*)
  \<and> leftFrom (fst(topT p)) (snd(topT p)) (*a ist links von b*)
  \<and> leftFrom (fst(bottomT p)) (snd(bottomT p)) (*c ist links von d*) 
  \<and> xCoord (leftP p) \<ge> xCoord (fst(topT p)) \<and> xCoord (leftP p) \<ge> xCoord (fst(bottomT p)) (*e \<ge> a \<and> c*)
  \<and> xCoord (rightP p) \<le> xCoord (snd(topT p)) \<and> xCoord (rightP p) \<le> xCoord (snd(bottomT p))(*f \<le> b \<and> d*)"

(*e < b \<and> d*)
lemma trapezHasOrderetPoints1: "trapezPointsXOrder p \<Longrightarrow>
  leftFrom (leftP p)(snd(topT p)) \<and> leftFrom (leftP p) (snd(bottomT p))"
  apply (simp add: leftFrom_def)
using leftFrom_def Orderings.xt1(8) trapezPointsXOrder_def by blast
(*f > a \<and> c*)
lemma trapezHasOrderetPoints2: "trapezPointsXOrder p \<Longrightarrow>
  leftFrom (fst(topT p)) (rightP p) \<and> leftFrom(fst(bottomT p)) (rightP p)"
  using leftFrom_def trapezPointsXOrder_def by auto
(*a < d*)
lemma trapezHasOrderetPoints3:"trapezPointsXOrder T \<Longrightarrow>leftFrom (fst(topT T)) (snd(bottomT T))"
  by (auto simp add: trapezPointsXOrder_def leftFrom_def)
(*b > c*)
lemma trapezHasOrderetPoints4:"trapezPointsXOrder T \<Longrightarrow>leftFrom (fst(bottomT T)) (snd(topT T))"
  by (auto simp add: trapezPointsXOrder_def leftFrom_def)

(*e ist zwischen ab und cd oder e=a oder e=c*)
definition trapezQuad:: "trapez \<Rightarrow> bool" where
  "trapezQuad p \<equiv>
  (rightTurn (fst(topT p)) (snd(topT p)) (leftP p) \<or> fst(topT p) = (leftP p)) (*e ist zwischen ab und cd*)
    \<and> (leftTurn (fst(bottomT p)) (snd(bottomT p)) (leftP p) \<or> fst(bottomT p) = (leftP p))
    \<and> (rightTurn (fst(topT p)) (snd(topT p)) (rightP p) \<or> snd(topT p) = (rightP p))(* und f ist zwischen ab und cd*)
    \<and> (leftTurn (fst(bottomT p)) (snd(bottomT p)) (rightP p) \<or> snd(bottomT p) = (rightP p))
    \<and> fst(topT p) \<noteq> fst(bottomT p) \<and> snd(topT p) \<noteq> snd(bottomT p) (*a\<noteq>c \<and> b\<noteq>d*)
    \<and> rightTurn (fst(topT p)) (snd(topT p)) (fst(bottomT p))(*a und b über c und d*)
    \<and> rightTurn (fst(topT p)) (snd(topT p)) (snd(bottomT p))"

lemma trapezTriangleVertex1: "trapezQuad p \<Longrightarrow>
  leftTurn (fst(bottomT p)) (snd(bottomT p)) (snd(topT p))
  \<and> leftTurn (fst(bottomT p)) (snd(bottomT p)) (fst(topT p))"
oops

(*eine der vertikalen Seiten des Trapezes ist ein Punkt*)
definition trapezTriangle :: "trapez \<Rightarrow> bool" where
   "trapezTriangle p \<equiv> (leftTurn (fst(bottomT p)) (snd(bottomT p)) (fst(topT p)) (*a ist über cd*)
    \<and> (leftTurn (fst(bottomT p)) (snd(bottomT p)) (leftP p) \<or> fst(bottomT p) = leftP p) (*e ist über cd*)
    \<and> (rightTurn (fst(topT p)) (snd(topT p)) (leftP p) \<or> fst(topT p) = leftP p) (*e ist unter a b*)
    \<and> snd(bottomT p) = snd(topT p) \<and> snd(bottomT p) = rightP p  (*und d=b=f*)
   )\<or>
   (fst(topT p) = fst(bottomT p) \<and> fst(bottomT p) = leftP p (*a=c=e*)
    \<and> leftTurn (fst(bottomT p)) (snd(bottomT p)) (snd(topT p)) (*b über c d*)
    \<and> (rightTurn (fst(topT p)) (snd(topT p)) (rightP p) \<or> snd(topT p) = rightP p) (*f ist unter a b*)
    \<and> (leftTurn (fst(bottomT p)) (snd(bottomT p)) (rightP p) \<or> snd(bottomT p) = rightP p))" (*f ist über c d*)

lemma trapezTriangleVertex: "trapezTriangle p \<Longrightarrow> 
  (leftTurn (fst(bottomT p)) (snd(bottomT p)) (snd(topT p)) \<and> fst(topT p) = fst(bottomT p))
  \<or> (leftTurn (fst(bottomT p)) (snd(bottomT p)) (fst(topT p)) \<and> snd(topT p) = snd(bottomT p))"
by (auto simp add: trapezTriangle_def)

(*Definition für Trapez ((a,b),(c,d),e,f)) top: (a,b), bottom:(c,d), leftP:e, rightP: f
  a=fst(fst p), b = snd(fst p), c=fst(fst(snd p)), d=snd(fst(snd p)), e=fst(snd(snd p)), f=snd(snd(snd p))*)
definition "isTrapez T \<equiv> trapezPointsXOrder T \<and> (trapezQuad T \<or> trapezTriangle T)"
definition trapezList :: "trapez list \<Rightarrow> bool" where "trapezList TM \<equiv> \<forall> t \<in> set TM. isTrapez t"

(*linke Ecke ist links von der rechten Ecke*)
lemma leftPRigthFromRightP [simp] : "isTrapez T \<Longrightarrow> leftFrom (leftP T) (rightP T)"
  by (simp add: isTrapez_def trapezPointsXOrder_def)
(*Linke Ecken sind rechts von den rechten Ecken*)
lemma trapezNeighbour1 : "isTrapez T \<Longrightarrow> isTrapez Ts \<Longrightarrow> rightP T = leftP Ts \<Longrightarrow>
  leftFrom (rightP T) (rightP Ts)"
  by (cases T, simp)
lemma trapezNeighbour2 : "isTrapez T \<Longrightarrow> isTrapez Ts \<Longrightarrow> rightP T = leftP Ts \<Longrightarrow>
  leftFrom (leftP T) (leftP Ts)"
  by (metis leftPRigthFromRightP)


(*e < b \<and> d*)
lemma leftPRigthFromRightP1: "isTrapez p \<Longrightarrow> leftFrom (leftP p)(snd(topT p))
  \<and> leftFrom (leftP p) (snd(bottomT p))"
  apply (cases p, simp add: leftFrom_def)
by (simp add: isTrapez_def leftFrom_def trapezPointsXOrder_def)
(*f > a \<and> c*)
lemma trapezHasOrderetPoints6: "isTrapez p \<Longrightarrow>leftFrom (fst(topT p)) (rightP p)
  \<and> leftFrom(fst(bottomT p)) (rightP p)"
  by (metis isTrapez_def trapezHasOrderetPoints2)
(*a < d*)
lemma trapezHasOrderetPoints7:"isTrapez T \<Longrightarrow> leftFrom (fst(topT T)) (snd(bottomT T))"
  by (metis isTrapez_def trapezHasOrderetPoints3)
(*b > c*)
lemma trapezHasOrderetPoints8:"isTrapez T \<Longrightarrow> leftFrom (fst(bottomT T)) (snd(topT T))"
  by (metis isTrapez_def trapezHasOrderetPoints4)


(*(*jeder Punkt der auf der xCoordinate von rightP steht und von topT und bottomT eingegrenzt wird*)
definition pointOnLeftT :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where
  "pointOnLeftT T p \<equiv> rightTurn (fst(topT T)) (snd(topT T)) p
    \<and> leftTurn (fst(bottomT T)) (snd(bottomT T)) p \<and> xCoord (leftP T) = xCoord p"
definition pointOnRightT :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where
  "pointOnRightT T p \<equiv> rightTurn (fst(topT T)) (snd(topT T)) p
    \<and> leftTurn (fst(bottomT T)) (snd(bottomT T)) p \<and> xCoord (rightP T) = xCoord p"
lemma pointNotOnLeftRightT[dest]: "pointOnLeftT T p \<Longrightarrow> pointOnRightT T p \<Longrightarrow> False"
  apply (simp add: pointOnLeftT_def pointOnRightT_def isTrapez_def trapezPointsXOrder_def)
by (metis leftFrom_def leftPRigthFromRightP1 less_irrefl)*)


(*topT und bottomT sind segmente*)
lemma topTSegment [simp]: "isTrapez T \<Longrightarrow> segment (fst(topT T)) (snd(topT T))"
  apply (cases T, subgoal_tac "xCoord (fst(topT T)) \<noteq> xCoord (snd(topT T))")
  apply (simp add: isTrapez_def)
by (metis isTrapez_def leftFrom_def not_less trapezHasOrderetPoints6 trapezPointsXOrder_def)
lemma bottomTSegment [simp]: "isTrapez T \<Longrightarrow> segment (fst(bottomT T)) (snd(bottomT T))"
  apply (cases T, subgoal_tac "xCoord (fst(bottomT T)) \<noteq> xCoord (snd(bottomT T))")
  apply (simp add: isTrapez_def)
by (metis  isTrapez_def leftFrom_def not_le trapezHasOrderetPoints2 trapezPointsXOrder_def)
lemma foo: "c \<noteq> d \<Longrightarrow> leftFrom c d \<Longrightarrow> leftFrom a b \<Longrightarrow> rightTurn a b c \<Longrightarrow>
  rightTurn a b d \<Longrightarrow> leftFrom a d \<Longrightarrow> leftFrom c b\<Longrightarrow> leftTurn c d a \<or> leftTurn c d  b"
  apply (case_tac "lineSeparate a b c d") using lineSeparate_def apply auto[1]
  apply (case_tac "lineSeparate c d a b") using lineSeparate_def apply auto[1]
  apply (subgoal_tac "\<not>collinear c b d")
  apply (case_tac "collinear a c d", rule disjI2)
  apply (case_tac "leftFrom d b")
oops
  
(*Beweise über die Positionen der Ecken vom Trapez*)
(*engegengesetzte Ecken des Trapezes sind von einander ungleich*)
lemma trapezVertex: "isTrapez p \<Longrightarrow> snd(topT p) \<noteq> fst(bottomT p) \<and> snd(bottomT p) \<noteq> fst(topT p)"
  by (metis leftFromDest trapezHasOrderetPoints7 trapezHasOrderetPoints8)
(*mind. einer der Ecken von topT ist über bottomT*)
lemma topAboveBottom [intro]:"isTrapez T \<Longrightarrow>
  leftTurn (fst (bottomT T)) (snd (bottomT T)) (fst (topT T)) 
  \<or> leftTurn (fst (bottomT T)) (snd (bottomT T)) (snd (topT T))"
  apply (auto simp add: isTrapez_def)
oops
(*leftP ist über bottom T oder ist die linke Ecke von bottomT*)
lemma leftPPos[intro]:"isTrapez T \<Longrightarrow> leftTurn (fst(bottomT T)) (snd(bottomT T)) (leftP T)
  \<or> (fst(bottomT T) = leftP T)"
  apply (simp add: leftP_def bottomT_def del: leftRightTurn leftTurnRotate leftTurnRotate2,
    cases T, simp del: leftRightTurn leftTurnRotate leftTurnRotate2)
by (metis bottomT_def isTrapez_def leftP_def trapezQuad_def trapezTriangle_def)

lemma rightPPos [intro] : "isTrapez T \<Longrightarrow> rightTurn (fst(topT T)) (snd(topT T)) (rightP T)
  \<or> (snd(topT T) = rightP T)"
  apply (simp add: leftP_def bottomT_def del: leftRightTurn leftTurnRotate leftTurnRotate2,
   cases T, simp del: leftRightTurn leftTurnRotate leftTurnRotate2)
by(metis isTrapez_def rightTurnRotate trapezQuad_def trapezTriangle_def)


definition neighbor :: "trapez \<Rightarrow> trapez \<Rightarrow> bool" where
  "isTrapez T \<Longrightarrow> isTrapez Tr \<Longrightarrow> neighbor T Tr \<equiv> rightP T = leftP Tr
  \<and> (topT T = topT Tr \<or> bottomT T = bottomT Tr)"
lemma neighborRightPSimp[simp]: "isTrapez T \<Longrightarrow> isTrapez Tr \<Longrightarrow> neighbor T Tr \<Longrightarrow>
  leftFrom (rightP T) (rightP Tr)"
  by (simp add: neighbor_def)
lemma neighborSam[dest]: "isTrapez T \<Longrightarrow> isTrapez Tr \<Longrightarrow> neighbor T T \<Longrightarrow> False"
  apply (simp add: neighbor_def, cases T, simp add: isTrapez_def)
  apply (simp add: trapezPointsXOrder_def)
by (metis leftFromDest)
lemma neighborNotSym[dest]:"isTrapez T \<Longrightarrow> isTrapez Tr \<Longrightarrow>neighbor T Tr \<Longrightarrow> neighbor Tr T \<Longrightarrow> False"
  apply (simp add: neighbor_def, cases T, simp add: isTrapez_def)
  apply (simp add: trapezPointsXOrder_def)
by (metis leftFromDest)
(*zwei Trapeze sind benachbart entland der Strecke PQ, wenn :
  - die linke Ecke eines Trapezes gleich der rechten Ecke des anderen Trapezes
  - topT gleich sind, falls PQ über rightPT bzw. bottomT gleich sind, falls PQ unter rightP.*)
definition neighborAlongSeg :: "trapez \<Rightarrow> trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "leftFrom P Q \<Longrightarrow> isTrapez T \<Longrightarrow> isTrapez Tr \<Longrightarrow>neighborAlongSeg T Ts P Q \<equiv> rightP T = leftP Ts \<and>
  ((rightTurn P Q (rightP T) \<and> topT T = topT Ts)
    \<or> (leftTurn P Q (rightP T) \<and> bottomT T = bottomT Ts))"
lemma neighborTrapezSame[dest]: "leftFrom P Q \<Longrightarrow> isTrapez T \<Longrightarrow> isTrapez Tr \<Longrightarrow>
  neighborAlongSeg T T P Q \<Longrightarrow> False"
  apply (auto simp add: neighborAlongSeg_def)
by (simp add: isTrapez_def leftFrom_def trapezPointsXOrder_def)+


(*ein Punkt P ist im Trapez T, wenn es auf den Kanten liegt, oder innerhalb des T*)
(*stimmt, weil von Vertikalen eingegrenzt*)
definition pointInTrapez :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where 
  "isTrapez T \<Longrightarrow> pointInTrapez T P \<equiv> xCoord P \<le> xCoord (rightP T) \<and> xCoord P \<ge> xCoord (leftP T)
  \<and> signedArea (fst(bottomT T)) (snd(bottomT T)) P \<ge> 0 \<and> signedArea (fst(topT T)) (snd(topT T)) P \<le> 0"
lemma pointInTrapezSimp[simp]: "isTrapez T \<Longrightarrow> pointInTrapez T P \<Longrightarrow> xCoord (rightP T) \<ge> xCoord P"
  by(simp add: pointInTrapez_def)
(*Punkt ist im Trapez, aber nicht auf den Kanten*)
definition pointInTrapezInner :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where 
  "isTrapez T \<Longrightarrow> pointInTrapezInner T P \<equiv> xCoord P \<le> xCoord (rightP T) \<and> xCoord P \<ge> xCoord (leftP T)
  \<and> leftTurn (fst(bottomT T)) (snd(bottomT T)) P  \<and> rightTurn (fst(topT T)) (snd(topT T)) P
  \<and> P \<noteq> rightP T \<and> P \<noteq> leftP T"
lemma InnerToPointInTrapez[simp]: "isTrapez T \<Longrightarrow> pointInTrapezInner T P \<Longrightarrow> pointInTrapez T P"
  apply (auto simp add: pointInTrapez_def pointInTrapezInner_def)
  using rightTurn_def apply auto[1] using rightTurn_def apply auto[1]
done

(*definition trapezSegmentIntersect :: "trapez \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
  "trapezSegmentIntersect T P Q \<equiv> intersect (fst (topT T)) (snd (topT T)) P Q
    \<or> intersect (fst (bottomT T)) (snd (bottomT T)) P Q \<or> "*)



(*********rBox. 4 Eckige Box um pointListe herum. First Trapez*)
(*Definition wann ist R eine rechteckige Box um PL herum*)
(*lassen sich die 3 pointInTrapez definitionen vereinheitlichen?*)
definition pointInRBox :: "trapez \<Rightarrow> point2d \<Rightarrow> bool" where 
  "isTrapez R \<Longrightarrow> pointInRBox R P \<equiv> leftFrom P (rightP R) \<and> (leftFrom (leftP R) P)
  \<and> leftTurn (fst(bottomT R)) (snd(bottomT R)) P \<and> (rightTurn (fst(topT R)) (snd(topT R)) P)"
definition rBoxTrapezS :: "point2d list \<Rightarrow> trapez \<Rightarrow> bool" where
  "rBoxTrapezS PL R \<equiv> (\<forall> a \<in> set PL. pointInRBox R a) \<and> isTrapez R"
lemma rBoxTrapezSSimp[simp]: "isTrapez R \<Longrightarrow> rBoxTrapezS [a] R = pointInRBox R a"
  by (auto simp add: rBoxTrapezS_def)
lemma rBoxTrapezSConcat: "rBoxTrapezS (concat PL) R \<Longrightarrow> i < length PL \<Longrightarrow> rBoxTrapezS (PL!i) R"
  apply (subgoal_tac "\<forall> a \<in> set (concat PL). pointInRBox R a")
by (auto simp add: rBoxTrapezS_def)
lemma rBoxTrapezSConcatEq : "PL \<noteq> [] \<Longrightarrow>
  rBoxTrapezS (concat PL) R = (\<forall> i < length PL. rBoxTrapezS (PL!i) R)"
  apply (auto simp add: rBoxTrapezSConcat)
  apply (subgoal_tac "(\<forall> a \<in> set (concat PL). pointInRBox R a)")
  apply (auto simp add: rBoxTrapezS_def)
by (smt UN_iff in_set_conv_nth set_concat)+


lemma newTrapez[simp]: "isTrapez oT \<Longrightarrow> pointInRBox oT P \<Longrightarrow>
  isTrapez (Abs_trapez (topT oT, bottomT oT, leftP oT, P))"
  apply (cases oT, simp add: isTrapez_def, rule conjI)
  using isTrapez_def apply auto[1]
  apply (simp add: trapezPointsXOrder_def pointInRBox_def)
  using leftFrom_def apply auto[1]
  apply (simp add: pointInRBox_def leftFrom_def  trapezPointsXOrder_def)
  apply (erule conjE)
  apply (erule disjE, rule disjI1)
  apply (simp add: isTrapez_def pointInRBox_def trapezQuad_def)
  apply (subst (asm) trapezTriangle_def, simp)
  apply (erule disjE, erule conjE, simp)+
  apply (erule conjE, erule disjE)+ apply (erule conjE, simp)+
sorry
lemma newTrapez1[simp]: "isTrapez oT \<Longrightarrow> pointInRBox oT P \<Longrightarrow>
  isTrapez (Abs_trapez (topT oT, bottomT oT, P, rightP oT))"
sorry


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

lemma trapezoidalVertex[simp] : "leftFrom (leftP (getTrapez TM)) (leftP (upRNeighb TM))"
  by (metis Rep_trapezoidal getTrapez_def isTrapezoidal_def leftPRigthFromRightP mem_Collect_eq
    neighbor_def upRNeighb_def)
lemma trapezoidalVertex1[simp] : "leftFrom (leftP (getTrapez TM)) (leftP (btRNeighb TM))"
  by (metis Rep_trapezoidal getTrapez_def isTrapezoidal_def leftPRigthFromRightP mem_Collect_eq
    neighbor_def btRNeighb_def)*)
  

end
