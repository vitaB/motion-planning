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

(*Wandle DAG in eine Trapez-Liste um*)
fun tDagList :: "tDag \<Rightarrow> trapez list" where
  "tDagList (Tip a) = [a]"
  | "tDagList (Node Tl x Tr) = ((tDagList Tl)@(tDagList Tr))"

(*wann ist ein Trapez im Baum*)
primrec tipInDag :: "trapez \<Rightarrow> tDag \<Rightarrow> bool" where
  "tipInDag T (Tip D) = (if (T = D) then True else False)"
  | "tipInDag T (Node Tl x Tr) = (tipInDag T Tl \<or> tipInDag T Tr)"

lemma tDagListComplete: "tipInDag T D \<longleftrightarrow> T \<in> set (tDagList D)" by (induction D, auto)
lemma tDagListNotEmpty[dest] : "tDagList D = [] \<Longrightarrow> False" by (induction D, auto)

(*wann ist ein Punkt im tDag*)
definition pointInDag :: "tDag \<Rightarrow> point2d \<Rightarrow> bool" where
  "pointInDag D A \<equiv> \<exists> X \<in> set (tDagList D). pointInTrapez X A"
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
lemma replaceTipSame [simp] : "replaceTip oT (Tip oT) D = D"
  by (induction oT "(Tip oT)" D rule: replaceTip.induct, simp+)
theorem replaceTipSimp [simp] :"\<not>tipInDag nT' D \<Longrightarrow>
  replaceTip nT' nT (replaceTip oT (Tip nT') D) = replaceTip oT nT D"
  apply (induction D, case_tac "nT' = x", simp+)
done

lemma replaceTipSize1: "size (replaceTip oT (Tip nT) D) = size D"
  by (induction oT "Tip nT" D rule: replaceTip.induct, simp+)
lemma replaceTipSize: "size (replaceTip oT nT D) \<ge> size D"
  by (induction oT nT D rule: replaceTip.induct, simp+)
(*keine unendliche regression*)
lemma "a\<noteq>b \<Longrightarrow> replaceTip a (Node (Tip a) (xNode (c)) (Tip b)) (Node (Tip a) (xNode (c)) (Tip b))
  = (Node ((Node (Tip a) (xNode (c)) (Tip b))) (xNode (c)) (Tip b))" by (auto)


lemma replaceMiss [simp]: "\<not>tipInDag oT D \<Longrightarrow> replaceTip oT nT D = D"
  by (induction oT nT D rule: replaceTip.induct, case_tac "oT = D", simp+)
lemma replaceAfter: "\<not>tipInDag oT nT \<Longrightarrow> \<not>tipInDag oT (replaceTip oT nT D)"
  by (induction oT nT D rule: replaceTip.induct, simp+)
lemma replaceAfter1 : "tipInDag oT nT \<Longrightarrow> tipInDag oT D \<Longrightarrow> tipInDag oT (replaceTip oT nT D)"
  by (induction oT nT D rule: replaceTip.induct,case_tac "oT = D", auto)
lemma replaceInDWithD [simp] : "tipInDag a D \<Longrightarrow> tipInDag a (replaceTip a D D)"
  by (auto simp add: replaceAfter1)










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