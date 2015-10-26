theory tDag
imports trapez
begin

(******directed acyclic graph*)
(*Knoten des graphen kann enweder ein Endpunkt sein, oder ein Segment*)
datatype kNode = xNode "point2d" | yNode "(point2d\<times>point2d)"

(*x-nodes stores a segment endpoint that defines a vertical extension in the trapezoid map,
and has leftChild and rightChild pointers to nodes.*)
(*y-node stores a line segment and its children are also recorded by the pointers are aboveChild
and belowChild depending on whether the child item is above or below the segment stored at the y-node.*)
datatype tDag = Tip "trapez" | Node "tDag" kNode "tDag"

(*liest alle xNodes aus tDag aus*)
fun xDagList :: "tDag \<Rightarrow> point2d list" where
  "xDagList (Tip a) = []"
  | "xDagList (Node Tl (xNode x) Tr) = xDagList Tl @ [x] @ xDagList Tr"
  | "xDagList (Node Tl (yNode x) Tr) = xDagList Tl @ xDagList Tr"
(*wenn a in tDag, dann ist a entweder im linken oder im rechten Teilbaum*)
lemma xDagListElem[intro]: "a \<in> set (xDagList (Node Tl x Tr)) \<Longrightarrow> a \<in> set (xDagList Tl)
  \<or> xNode a = x  \<or> a \<in> set (xDagList Tr)"
  by (case_tac "(Node Tl x Tr)" rule: xDagList.cases, auto)

(*wenn a in tDag, dann ist a auch in der Erweiterung von tDag*)
lemma xDagListAppendLt[intro]:"a \<in> set (xDagList Tl) \<Longrightarrow> a \<in> set (xDagList (Node Tl x Tr))"
  apply (induct Tl rule: xDagList.induct, simp)
by (smt append_Cons append_assoc in_set_conv_decomp kNode.exhaust xDagList.simps(2)
    xDagList.simps(3))+
lemma xDagListAppendRt[intro]:"a \<in> set (xDagList Tr) \<Longrightarrow> a \<in> set (xDagList (Node Tl x Tr))"
  apply (induct Tr rule: xDagList.induct, simp)
by (smt append_Cons append_assoc in_set_conv_decomp kNode.exhaust xDagList.simps(2)
    xDagList.simps(3))+

(*liest alle y-Nodes aus tDag aus*)
fun yDagList :: "tDag \<Rightarrow> (point2d\<times>point2d) list" where
  "yDagList (Tip a) = []"
  | "yDagList (Node Tl (xNode x) Tr) = yDagList Tl @ yDagList Tr"
  | "yDagList (Node Tl (yNode x) Tr) = yDagList Tl @ [x] @ yDagList Tr"
(*wenn a in tDag, dann ist a entweder im linken oder im rechten Teilbaum*)
lemma yDagListElem[intro]: "a \<in> set (yDagList (Node Tl x Tr)) \<Longrightarrow> a \<in> set (yDagList Tl)
  \<or> yNode a = x  \<or> a \<in> set (yDagList Tr)"
  by (case_tac "(Node Tl x Tr)" rule: yDagList.cases, auto)

(*wenn a in tDag, dann ist a auch in der Erweiterung von tDag*)
lemma yDagListAppendLt[intro]:"a \<in> set (yDagList Tl) \<Longrightarrow> a \<in> set (yDagList (Node Tl x Tr))"
  apply (induct Tl rule: yDagList.induct, simp)
by (smt append_Cons append_assoc in_set_conv_decomp kNode.exhaust yDagList.simps(2)
    yDagList.simps(3))+
lemma yDagListAppendRt[intro]:"a \<in> set (yDagList Tr) \<Longrightarrow> a \<in> set (yDagList (Node Tl x Tr))"
  apply (induct Tr rule: yDagList.induct, simp)
by (smt append_Cons append_assoc in_set_conv_decomp kNode.exhaust yDagList.simps(2)
    yDagList.simps(3))+

(*Wandle DAG in eine Trapez-Liste um*)
fun tDagList :: "tDag \<Rightarrow> trapez list" where
  "tDagList (Tip a) = [a]"
  | "tDagList (Node Tl x Tr) = ((tDagList Tl)@(tDagList Tr))"
(*tDagList kann nicht leer sein*)
lemma tDagListNotEmpty[dest] : "tDagList D = [] \<Longrightarrow> False" by (induction D, auto)
(*wenn a in tDag, dann ist a entweder im linken oder im rechten Teilbaum*)
lemma tDagListElem[intro]: "a \<in> set (tDagList (Node Tl x Tr)) \<Longrightarrow>
  a \<in> set (tDagList Tl) \<or> a \<in> set (tDagList Tr)"
  by (case_tac "(Node Tl x Tr)" rule: tDagList.cases, auto)

(*wenn a in tDag, dann ist a auch in der Erweiterung von tDag*)
lemma tDagListAppendLt[intro]:"a \<in> set (tDagList Tl) \<Longrightarrow> a \<in> set (tDagList (Node Tl x Tr))"
  apply (induct Tl rule: tDagList.induct, simp)
by (smt append_Cons append_assoc in_set_conv_decomp kNode.exhaust tDagList.simps(2))+
lemma tDagListAppendRt[intro]:"a \<in> set (tDagList Tr) \<Longrightarrow> a \<in> set (tDagList (Node Tl x Tr))"
  apply (induct Tr rule: tDagList.induct, simp)
by (smt append_Cons append_assoc in_set_conv_decomp kNode.exhaust tDagList.simps(2))+

(*alle Elemente von tDagList sind Trapeze, wenn tDagList ist trapezList*)
lemma trapezListTDag[simp]: "trapezList (tDagList D) \<Longrightarrow> T \<in> set (tDagList D) \<Longrightarrow> isTrapez T"
  by (simp add: trapezListSimp)

(*wann ist ein Trapez im Baum*)
primrec tipInDag :: "trapez \<Rightarrow> tDag \<Rightarrow> bool" where
  "tipInDag T (Tip D) = (if (T = D) then True else False)"
  | "tipInDag T (Node Tl x Tr) = (tipInDag T Tl \<or> tipInDag T Tr)"

(*wenn a in tDag, dann ist a entweder im linken oder im rechten Teilbaum*)
lemma tipInDagElem[intro]: "tipInDag a (Node Tl x Tr) \<Longrightarrow> tipInDag a Tl \<or> tipInDag a Tr"
  by (case_tac "(Node Tl x Tr)", auto)

(*wenn a in tDag, dann ist a auch in der Erweiterung von tDag*)
lemma tipInDagAppendRt[intro]:"tipInDag a Tr \<Longrightarrow> tipInDag a (Node Tl x Tr)"
  by(induct Tr, auto)
lemma tipInDagAppendLt[intro]:"tipInDag a Tl \<Longrightarrow> tipInDag a (Node Tl x Tr)"
  by(induct Tl, auto)

(*tipInDag and T is in tDagList is equivalent*)
lemma tDagListComplete: "tipInDag T D \<longleftrightarrow> T \<in> set (tDagList D)" by (induction D, auto)

(*List.count and tipInDag is equivalent*)
lemma countSubList[simp]: "List.count (A @ B) T = List.count A T + List.count B T"
  by (induct A, auto)
lemma countTipInDag: "tipInDag T D \<longleftrightarrow> List.count (tDagList D) T > 0"
  apply (auto, induct D)
    apply (case_tac "x=T", simp, simp)
  apply (auto)
using tDagListComplete by fastforce

(*wann ist ein Punkt im tDag*)
definition pointInDag :: "tDag \<Rightarrow> point2d \<Rightarrow> bool" where
  "pointInDag D A \<equiv> \<exists> X \<in> set (tDagList D). pointInTrapez X A"
lemma pointInDagSimp[simp]: "isTrapez R \<Longrightarrow> pointInDag (Tip R) p = pointInTrapez R p"
  by (simp add: pointInDag_def)
lemma pointInDagCompl: "pointInTrapez T A \<Longrightarrow> tipInDag T D \<Longrightarrow> pointInDag D A"
  apply (induct D, simp)
  using pointInDag_def tDagListComplete tipInDag.simps(1) apply blast
by (auto simp add: pointInDag_def)


(*Input Tip welches entfernt wird, tDag welches hinzugefügt wird, tDag-tree in dem ersetzt werden soll
Output: neues tDag-tree*)
(* wie verbiete ich replaceTip a D D?*)
fun replaceTip :: "trapez \<Rightarrow> tDag \<Rightarrow> tDag \<Rightarrow> tDag" where
  "replaceTip oT nT (Tip D) = (if (D = oT) then (nT) else (Tip D))"
 |"replaceTip oT nT (Node Tl x Tr) = Node (replaceTip oT nT Tl) x (replaceTip oT nT Tr)"

(*Trapez durch sich selber austauschen*)
lemma replaceTipSame[simp]: "replaceTip oT (Tip oT) D = D"
  by (induction oT "(Tip oT)" D rule: replaceTip.induct, simp+)
lemma replaceTipSame1[simp]: "replaceTip oT nT (Tip oT) = nT"
   by (induction oT nT "Tip oT" rule: replaceTip.induct, simp+)

(*trapez austauschen, dass in tDag nicht existiert*)
lemma replaceMiss [simp]: "\<not>tipInDag oT D \<Longrightarrow> replaceTip oT nT D = D"
  by (induction oT nT D rule: replaceTip.induct, case_tac "oT = D", simp+)
theorem replaceTipSimp [simp] :"\<not>tipInDag nT' D \<Longrightarrow>
  replaceTip nT' nT (replaceTip oT (Tip nT') D) = replaceTip oT nT D"
  apply (induction D, case_tac "nT' = x", simp+)
done


(*replaceTip and size of tDag*)
lemma replaceTipSize1: "size (replaceTip oT (Tip nT) D) = size D"
  by (induction oT "Tip nT" D rule: replaceTip.induct, simp+)
lemma replaceTipSize: "size (replaceTip oT nT D) \<ge> size D"
  by (induction oT nT D rule: replaceTip.induct, simp+)


(*tipInDag nach raplaceTip*)
lemma replaceAfter: "\<not>tipInDag oT nT \<Longrightarrow> \<not>tipInDag oT (replaceTip oT nT D)"
  by (induction oT nT D rule: replaceTip.induct, simp+)
lemma replaceAfter1 : "tipInDag oT nT \<Longrightarrow> tipInDag oT D \<Longrightarrow> tipInDag oT (replaceTip oT nT D)"
  by (induction oT nT D rule: replaceTip.induct,case_tac "oT = D", auto)
lemma replaceInDWithD [simp] : "tipInDag a D \<Longrightarrow> tipInDag a (replaceTip a D D)"
  by (auto simp add: replaceAfter1)


(*replaceTip and xDagList*)
lemma replaceTipXDagList[intro]: "a \<in> set (xDagList D) \<Longrightarrow> a \<in> set (xDagList (replaceTip oT nT D))"
  apply (induct oT nT D rule: replaceTip.induct, auto)
  apply (subgoal_tac "a \<in> set (xDagList Tl) \<or> a \<in> set (xDagList Tr) \<or> xNode a = x", safe)
  apply (simp, blast)+
  apply simp
using xDagListElem by blast
lemma replaceTipXDagList1[intro]: "a \<in> set (xDagList (replaceTip oT nT D)) \<Longrightarrow>
  a \<in> set (xDagList D) \<or> a \<in> set (xDagList nT)"
  apply (induct oT nT D rule: replaceTip.induct, auto)
by (metis append_Cons in_set_conv_decomp xDagList.simps(2) xDagListAppendLt xDagListAppendRt
  xDagListElem)
(*Anzahl der Elemente nach replaceTip*)
lemma "List.count (xDagList (replaceTip oT nT D)) b =
  List.count (xDagList D) b + (List.count (xDagList nT) b) * (List.count (tDagList D) oT)"
  apply (case_tac "\<not>tipInDag oT D", simp)
    using countTipInDag apply blast
  apply (induct D, auto)
oops 
lemma replaceCount: "\<forall> a. a \<in> set (xDagList nT) \<longrightarrow> a \<notin> set (xDagList D) \<Longrightarrow> b \<in> set (xDagList D)
  \<Longrightarrow> List.count (xDagList (replaceTip oT nT D)) b = List.count (xDagList D) b"
  apply (subgoal_tac "b \<notin> set (xDagList nT)")
  apply (induction oT nT D rule: replaceTip.induct, simp+)
oops
(*uniqueXCoord, xDagList and replaceTip*)
lemma replaceTipUniqueXPerm[simp]: "uniqueXCoord (xDagList D @ xDagList nT) \<Longrightarrow>
  uniqueXCoord (xDagList (replaceTip T nT D))"
oops


(*replaceTip and yDagList*)
lemma replaceTipYDagList[intro]: "a \<in> set (yDagList D) \<Longrightarrow> a \<in> set (yDagList (replaceTip oT nT D))"
  apply (induct oT nT D rule: replaceTip.induct, auto)
  apply (subgoal_tac "a \<in> set (yDagList Tl) \<or> a \<in> set (yDagList Tr) \<or> yNode a = x", safe)
  apply (simp, blast)+
  apply simp
using yDagListElem by blast
lemma replaceTipYDagList1[intro]: "a \<in> set (yDagList (replaceTip oT nT D)) \<Longrightarrow>
  a \<in> set (yDagList D) \<or> a \<in> set (yDagList nT)"
  apply (induct oT nT D rule: replaceTip.induct, auto)
  apply (cut_tac Tl="replaceTip oT nT Tl" and Tr="replaceTip oT nT Tr" and a=a and x=x
    in yDagListElem)
by (auto)


(*replaceTip and tDagList*)
lemma replaceTipTDagList[intro]: "a \<in> set (tDagList (replaceTip oT nT D)) \<Longrightarrow>
  a \<in> set (tDagList D) \<or> a \<in> set (tDagList nT)"
by (induct oT nT D rule: replaceTip.induct, auto)










(*alte Definition*)

(*definition tDagIsTrapMap :: "tDag \<Rightarrow> bool" where
  "tDagIsTrapMap D \<equiv> (\<forall> a. pointInDag D a \<longrightarrow> pointInTrapez (queryTrapezoidMap D a) a)
  \<and> (\<forall> i < length (tDagList D). isTrapez ((tDagList D)!i))"

typedef trapMap = "{D::tDag. tDagIsTrapMap D}"
  apply(auto, simp add: pointInDag_def tDagIsTrapMap_def) sorry
lemma trapMapSimp1[simp]: "tDagIsTrapMap D \<Longrightarrow> Rep_trapMap (Abs_trapMap D) = D"
  by (simp add: Abs_trapMap_inverse)
definition trapMapDag :: "trapMap \<Rightarrow> tDag" where "trapMapDag D \<equiv> Rep_trapMap D"
lemma trapMapDagSimp[simp]: "tDagIsTrapMap D \<Longrightarrow> trapMapDag (Abs_trapMap D) = D"
  by (simp add: trapMapDag_def)*)

(*(*order for tDag*)
(*jedes Trapez dessen rightP \<le> x ist ist im Tl von Tl x Tr*)
fun tDagOrdX1 :: "tDag \<Rightarrow> real \<Rightarrow> bool" where
  "tDagOrdX1 (Tip T) x = (xCoord(rightP T) \<le> x)"
  | "tDagOrdX1 (Node lf (xNode n) rt) x = (tDagOrdX1 lf x \<and> xCoord n < x)"
  | "tDagOrdX1 (Node lf (yNode n) rt) x = tDagOrdX1 lf x"
fun tDagOrdX2 :: "tDag \<Rightarrow> real \<Rightarrow> bool" where
  "tDagOrdX2 (Tip T) x = (xCoord(leftP T) \<ge> x)"
  | "tDagOrdX2 (Node lf (xNode n) rt) x = (tDagOrdX2 lf x \<and> x > xCoord n)"
  | "tDagOrdX2 (Node lf (yNode n) rt) x = tDagOrdX2 lf x"
fun tDagOrdX :: "tDag \<Rightarrow> bool" where
  "tDagOrdX (Tip T) = True"
  | "tDagOrdX (Node lf (xNode n) rt) = (tDagOrdX1 lf (xCoord n) \<and> tDagOrdX2 rt (xCoord n)
    \<and> tDagOrdX lf \<and> tDagOrdX rt)"
  | "tDagOrdX (Node lf (yNode n) rt) = (tDagOrdX lf \<and> tDagOrdX rt)"
fun tDagOrdY :: "tDag \<Rightarrow> (point2d*point2d) \<Rightarrow> bool" where
  "tDagOrdY (Tip T) y = (signedArea (fst y) (snd y) (rightP T) \<ge> 0)"
  | "tDagOrdY (Node lf (yNode n) rt) y = (tDagOrdY lf y
    \<and> signedArea (fst y) (snd y) (fst y) > 0 \<and> signedArea (fst y) (snd y) (snd y) > 0)"
  | "tDagOrdY (Node lf (xNode n) rt) y = tDagOrdY lf y"
fun tDagOrdY1 :: "tDag \<Rightarrow> (point2d*point2d) \<Rightarrow> bool" where
  "tDagOrdY1 (Tip T) y = (signedArea (fst y) (snd y) (rightP T) \<le> 0)"
  | "tDagOrdY1 (Node lf (yNode n) rt) y = (tDagOrdY1 lf y
    \<and> signedArea (fst y) (snd y) (fst y) < 0 \<and> signedArea (fst y) (snd y) (snd y) < 0)"
  | "tDagOrdY1 (Node lf (xNode n) rt) y = tDagOrdY1 lf y"
(*jedes Trapez in tDag ist so aufgebaut, dass für alle Trapeze im Baum (Node lf k rt) gilt:
  -rechteEcke von Trapez ist links von k
  -rechteEcke ist über der Kante k *)
fun tDagOrdMap :: "tDag \<Rightarrow> bool" where
  "tDagOrdMap (Tip T)  = True"
  | "tDagOrdMap (Node lf (xNode x) rt) = (tDagOrdX lf \<and> tDagOrdX rt)"
  | "tDagOrdMap (Node lf (yNode y) rt) = (tDagOrdY lf y \<and> tDagOrdY1 rt y)"
lemma "tDagOrdMap (Node lf (xNode x) rt) \<Longrightarrow>
  i < length (tDagList lf) \<Longrightarrow> xCoord (rightP ((tDagList lf)!i)) \<le> xCoord x"
  apply (auto)
  apply (induction lf "xCoord x" rule: tDagOrdX.induct, auto)
oops*)
end