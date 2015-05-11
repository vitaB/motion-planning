theory segmentList
imports line
begin

(*zusammenhängende strecken, mit mehr als 2 Ecken. jede Ecke kommt nur ein mal vor.
hat damit also nur 2 Nachbarn*)
definition pointList :: "point2d list \<Rightarrow> bool" where
"pointList L \<equiv> (size L \<ge> 3 \<and> distinct L)"

(*keine der Ecken kann sich wiederholen*)
lemma distEdge : "pointList P \<Longrightarrow> \<forall> a b::point2d. a \<in> set P \<and> b \<in> set P \<and> a \<noteq> b \<longrightarrow> \<not> pointsEqual a b"
by (auto simp add: pointsEqual_def)

(*lemma distVertex : ""*)





(* Line/Segment soll kein eigener Datentyp mehr sein!
(*gibt punkt Liste als SegmentListe zurück*)
fun segList :: "point2d list \<Rightarrow> line list" where
  "segList [] = []"
| "segList [x] = []"
| "segList (x#y#xs) =  (\<lparr>sPoint= x, ePoint= y\<rparr>) # (segList (y#xs))"
lemma segList1 : "pointList (x#y#xs) \<longrightarrow> segList (x#y#xs) = (\<lparr>sPoint= x, ePoint= y\<rparr>) # (segList (y#xs))"
by auto
lemma segListapp : "pointList P  \<Longrightarrow> a \<in> set (segList P) \<Longrightarrow> a \<in> set (segList (P @ p))"
sorry
lemma segmentList [simp] : "pointList P \<and> a \<in> set(segList P) \<longrightarrow> segment a"
  apply (auto)
  apply (induct P rule: segList.induct)
  apply (simp, simp)
  apply (simp only: segList.simps)
  apply (auto)
  apply (simp add: segment_def pointList_def)
sorry
lemma segListdistinct : "pointList P \<Longrightarrow> L = segList P \<Longrightarrow> a \<in> set(L) \<and> b \<in> set(L) \<and> a \<noteq> b
  \<longrightarrow> sPoint(a) \<noteq> sPoint(b) \<and> ePoint(a) \<noteq> ePoint(b)"
sorry

primrec inList :: "'a \<Rightarrow>'a list \<Rightarrow> bool" where
  "inList n [] = False"
| "inList n (x#xs) = (if x = n then True else inList n xs)"

(*keine der Strecken kann sich wiederholen*)
(*falsch! a und b müssen hinter einander stehen*)
lemma distVertex : "pointList P \<Longrightarrow> L = segList P \<Longrightarrow>
 \<forall> a b :: line. a \<in> set L \<and> b \<in> set L \<and> a \<noteq> b \<longrightarrow> segment a \<longrightarrow> segment b \<longrightarrow> \<not>segmentEqual a b "
  apply (rule allI,rule allI)
  apply (rule impI, rule impI, rule impI)
  apply (erule conjE, erule conjE)
  apply (simp add: segmentEqual_def)
  apply (rule impI)
  thm segList.cases
  apply (rule_tac x=P in segList.cases)
  apply (simp add: pointList_def)
  apply (simp)
oops
*)
end