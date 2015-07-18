(*Datentyp trapez und directed acyclic graph(dag)-struktur für Trapeze*)

theory tDag
imports rBox
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
definition trapezNotEq :: "trapez \<Rightarrow> trapez \<Rightarrow> bool" where
  "trapezNotEq A B \<equiv> A \<noteq> B"
definition leftT :: "trapez \<Rightarrow> (point2d*point2d)" where 
  "leftT T \<equiv> vertSegment (topT T) (bottomT T) (leftP T)"
definition rightT :: "trapez \<Rightarrow> (point2d*point2d)" where 
  "rightT T \<equiv> vertSegment (topT T) (bottomT T) (rightP T)"

(*evtl. überprüfung zu aufwendig*)
definition trapezCollinearFree :: "trapez \<Rightarrow> bool" where
  "trapezCollinearFree T \<equiv> \<not>collinearList[fst (leftT T), fst (rightT T), snd(rightT T), snd(leftT T)]"

(*Wann sind Trapeze Nachbarn*)
definition leftNeighbour :: "trapez \<Rightarrow> trapez \<Rightarrow> bool" where "leftNeighbour A B \<equiv> leftP A = rightP B"
definition rightNeighbour :: "trapez \<Rightarrow> trapez \<Rightarrow> bool" where "rightNeighbour A B \<equiv> leftP B = rightP A"
lemma neighbourTrans : "leftNeighbour A B = rightNeighbour B A "by (simp add: leftNeighbour_def rightNeighbour_def)
definition neighbour :: "trapez \<Rightarrow> trapez \<Rightarrow> bool" where "neighbour  A B \<equiv> leftNeighbour A B \<or> rightNeighbour A B"

(*wandle rBox in ein Trapez um*)
definition rBoxTrapez :: "point2d list \<Rightarrow> trapez" where 
  "pointList R \<Longrightarrow> length R = 4 \<Longrightarrow> cPolygon (cyclePath R) \<Longrightarrow>
  rBoxTrapez R \<equiv> Abs_trapez ((hd R,R!1),(R!3,R!2),hd R,R!2)"

(*lemma rBoxTrapezCollinearFree[simp]: "pointLists PL \<Longrightarrow> uniqueXCoord (concat PL) \<Longrightarrow> trapezCollinearFree (rBoxTrapez PL)"
  apply (simp add: trapezCollinearFree_def rBoxTrapez_def)
  apply (simp add: leftT_def rightT_def topT_def bottomT_def)
  apply (subgoal_tac "segment (fst ((fst (Rep_trapez (rBoxTrapez PL))))) (fst (fst (Rep_trapez (rBoxTrapez PL))))")
  apply (subgoal_tac "segment (fst (fst (snd (Rep_trapez (rBoxTrapez PL))))) (fst (fst (snd (Rep_trapez (rBoxTrapez PL)))))")
  apply (simp add: vertSegment_def)
sorry*)


(*Knoten des graphen kann enweder ein Endpunkt sein, oder ein Segment*)
datatype_new kNode = xNode "point2d" | yNode "(point2d\<times>point2d)"

(*directed acyclic graph*)
(*x-nodes stores a segment endpoint that defines a vertical extension in the trapezoid map,
and has leftChild and rightChild pointers to nodes.*)
(*y-node stores a line segment and its children are also recorded by the pointers are aboveChild
and belowChild depending on whether the child item is above or below the segment stored at the y-node.*)
datatype_new dag = Tip "trapez" | Node "dag" kNode "dag"

(*Wandle DAG in eine Trapez-Liste um*)
primrec dagList :: "dag \<Rightarrow> trapez list" where
  "dagList (Tip a) = [a]"
  | "dagList (Node Tl x Tr) = ((dagList Tl)@(dagList Tr))"

(*wann ist ein Trapez im Baum*)
fun tipInDag :: "trapez \<Rightarrow> dag \<Rightarrow> bool" where
  "tipInDag T (Tip D) = (if (T = D) then True else False)"
  | "tipInDag T (Node Tl x Tr) = (tipInDag T Tl \<or> tipInDag T Tr)"
lemma dagListComplete : "tipInDag T D \<longleftrightarrow> T \<in> set (dagList D)" by (induction D, auto)

(*Input Tip welches entfernt wird, dag welches hinzugefügt wird, dag-tree in dem ersetzt werden soll
Output: neues dag-tree*)
fun replaceTip :: "trapez \<Rightarrow> dag \<Rightarrow> dag \<Rightarrow> dag" where
  "replaceTip oT nT (Tip D) = (if (D = oT) then (nT) else (Tip D))"
 |"replaceTip oT nT (Node Tl x Tr) = Node (replaceTip oT nT Tl) x (replaceTip oT nT Tr)"

lemma replaceMiss [simp]: "\<not>tipInDag oT D \<Longrightarrow> replaceTip oT nT D = D"
  by (induction oT nT D rule: replaceTip.induct, case_tac "oT = D", simp+)
lemma replaceAfter: "\<not>tipInDag oT nT \<Longrightarrow> \<not>tipInDag oT (replaceTip oT nT D)"
  by (induction oT nT D rule: replaceTip.induct, simp+)

lemma replaceTipSize1 : "size (replaceTip oT (Tip nT) D) = size D"
  by (induction oT "Tip nT" D rule: replaceTip.induct, simp+)
lemma replaceTipSize : "size (replaceTip oT nT D) \<ge> size D"
  by (induction oT nT D rule: replaceTip.induct, simp+)

lemma replaceTipSame [simp] : "replaceTip oT (Tip oT) D = D"
  by (induction oT "(Tip oT)" D rule: replaceTip.induct, simp+)

lemma "nT\<noteq>D\<Longrightarrow> replaceTip oT nT D = replaceTip oT D nT \<Longrightarrow> False"
  apply (induction D, simp)
  apply (case_tac "x = oT")
oops
theorem replaceTipSimp [simp] :"\<not>tipInDag nT' D \<Longrightarrow> replaceTip nT' nT (replaceTip oT (Tip nT') D) = replaceTip oT nT D"
  apply (induction D, case_tac "nT' = x", simp+)
done
theorem "replaceTip oT nT (replaceTip oT' nT' D) = replaceTip oT' nT' (replaceTip oT nT D) \<Longrightarrow> False"
  apply (induction oT nT D rule: replaceTip.induct)
  apply (simp)
  apply (case_tac "oT'= oT")
  apply (case_tac "D = oT'")
  apply (simp)
oops


end
