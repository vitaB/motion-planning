theory segmentList
imports line
begin

lemma inInsort : "a \<in> set (insort_insert x xs) \<longleftrightarrow> a \<in> set (xs) \<or> a = x"
by (auto simp add: List.linorder_class.set_insort_insert)

(*zusammenhängende strecken, mit mehr als 2 Ecken. jede Ecke kommt nur ein mal vor.
hat damit also nur 2 Nachbarn*)
definition pointList :: "point2d list \<Rightarrow> bool" where
"pointList L \<equiv> (size L \<ge> 3 \<and> distinct L)"

(*keine der Ecken kann sich wiederholen*)
lemma distEdge : "pointList P \<Longrightarrow> \<forall> a b::point2d. a \<in> set P \<and> b \<in> set P \<and> a \<noteq> b \<longrightarrow> \<not> pointsEqual a b"
by (auto simp add: pointsEqual_def)

(*alle Kanten von pointList sind segmente*)
lemma pointsSegments : "\<forall> P::point2d list. a \<in> set P \<and> b \<in> set P \<and> a \<noteq> b \<longrightarrow> segment a b"
by (auto simp add: pointList_def segment_def pointsEqual_def)

(*keine der Kanten kann sich wiederholen*)
lemma distVertex : "pointList P \<Longrightarrow> \<forall> a b c d::point2d. a \<in> set P \<and> b \<in> set P \<and> c \<in> set P \<and> d \<in> set P
  \<and> a \<noteq> c \<and> a \<noteq> b \<and> c \<noteq> d \<longrightarrow> \<not> segment_Same a b c d"  
  apply (auto)
  apply (cut_tac a=a and b=b in pointsSegments) apply (erule_tac x=P in allE)
  apply (cut_tac a=c and b=d in pointsSegments) apply (erule_tac x=P in allE)
  apply (auto simp add: segment_Same_def distEdge)
done

(*Definiere ordnung von pointList nach x-Coord und nach y-Coord.*)
definition xCoordSorted :: "point2d list \<Rightarrow> point2d list" where
"xCoordSorted P \<equiv> sort_key (getX) P"
definition yCoordSorted :: "point2d list \<Rightarrow> point2d list" where
"yCoordSorted P \<equiv> sort_key (getY) P"

(*alle xCoordinaten sind in der neuen Liste*)
lemma inXCoord : "a \<in> set xs \<longrightarrow> a \<in> set (xCoordSorted xs)"
  by (auto simp add: xCoordSorted_def)

lemma inYCoord : "a \<in> set xs \<longrightarrow>  a \<in> set (yCoordSorted xs)"
  by (auto simp add: yCoordSorted_def)
  
(*xCoordSorted gibt eine sortierte Liste zurück*)
lemma xCoordSorted1 :  "sorted (map getX (xCoordSorted xs))"
  apply (induct xs)
  apply (auto simp:sorted_insort_key xCoordSorted_def)
by (metis getX_def map_eq_conv sort_key_simps(2) sorted_sort_key)
theorem xCoordSorted2 :  "xCoordSorted (x # xs) = (x # xs) \<longleftrightarrow> (sorted (map getX (xCoordSorted xs)) \<and> (\<forall> y \<in> set (xCoordSorted xs). getX x \<le> getX y))"
  apply (auto simp add: xCoordSorted1)
  apply (induct xs)
  apply (auto simp:sorted_insort_key xCoordSorted_def)
sorry
lemma yCoordSorted1 :  "sorted (map getY (yCoordSorted xs))"
  apply (induct xs)
  apply (auto simp:sorted_insort_key yCoordSorted_def)
by (metis getY_def map_eq_conv sort_key_simps(2) sorted_sort_key)
theorem yCoordSorted2 :  "yCoordSorted (x # xs) = (x # xs) \<longleftrightarrow> (sorted (map getY (yCoordSorted xs)) \<and> (\<forall> y \<in> set (yCoordSorted xs). getY x \<le> getY y))"
sorry

lemma xCoordOrd1 : "pointList L \<Longrightarrow> xCoord (last (xCoordSorted L)) \<ge> xCoord (hd (xCoordSorted L))"
  apply (cases L)
  apply (simp add: pointList_def)
sorry

lemma yCoordOrd1 : "pointList L \<Longrightarrow> yCoord (last (yCoordSorted L)) \<ge> yCoord (hd (yCoordSorted L))"
  apply (cases L)
  apply (simp add: pointList_def)
sorry






(*alte Definition*)

(*brauche ich die equivalente beschreibung mit insort_key noch?*)
(*fun xCoordSort :: "point2d list \<Rightarrow> point2d list" where
  "xCoordSort [] = []"
  | "xCoordSort (x#xs) = insort_key xCoord x (xCoordSort xs)" 
fun yCoordSort :: "point2d list \<Rightarrow> point2d list" where
  "yCoordSort [] = []"
  | "yCoordSort (x#xs) = insort_key yCoord x (yCoordSort xs)" 
lemma xCoordSort_right : "xCoordSorted P = xCoordSort P"
  apply (simp add: xCoordSorted_def)
  apply (induction P rule: xCoordSort.induct, simp)
  apply (simp)
done
lemma yCoordSort_right : "yCoordSorted P = yCoordSort P"
  apply (simp add: yCoordSorted_def)
  apply (induction P rule: yCoordSort.induct, simp)
  apply (simp)
done*)

(*for trapezoidalmap. Sollte noch mit Lambda abstrakter definiert werden*)
(*insort_insert damit neue Liste distinct ist*)
(*fun yCoordList ::  "point2d list \<Rightarrow> real list" where
"yCoordList [] = []" 
| "yCoordList (x#xs) = insort_insert (getY x) (yCoordList xs)"
fun xCoordList ::  "point2d list \<Rightarrow> real list" where
"xCoordList [] = []" 
| "xCoordList (x#xs) = insort_insert (getX x) (xCoordList xs)"*)

(*xCoordList gibt eine sortierte Liste zurück*)
(*lemma XCoordSorted : "sorted (xCoordList P)"
  apply (induct P rule: xCoordList.induct, simp)
  apply (simp add: sorted_insort_insert)
done
lemma YCoordSorted : "sorted (yCoordList P)"
  apply (induct P rule: yCoordList.induct, simp)
  apply (simp add: sorted_insort_insert)
done*)

(*alle xCoordinaten sind in der neuen Liste*)
(*lemma inXCoord : "a \<in> set xs \<longrightarrow> (getX a) \<in> set (xCoordList xs)"
  apply (rule impI)
  apply (induct xs rule: yCoordList.induct, simp)
  apply (simp, erule disjE, simp)
  apply (simp add: inInsort)
  apply (simp add: inInsort)
done
lemma inYCoord : "a \<in> set xs \<longrightarrow> (getY a) \<in> set (yCoordList xs)"
  apply (rule impI)
  apply (induct xs rule: xCoordList.induct, simp)
  apply (simp, erule disjE, simp)
  apply (simp add: inInsort)
  apply (simp add: inInsort)
done*)
(*xCoordList gibt eine sortierte Liste zurück*)
(*theorem XCoordSorted1 : "sorted (xCoordList (x # xs)) = (sorted (xCoordList xs) \<and> (\<forall> y \<in> set (xCoordList xs). getX x \<le> y))"
  apply (auto)
  apply (simp add: XCoordSorted)
sorry
theorem YCoordSorted1 : "sorted (yCoordList (x # xs)) = (sorted (yCoordList xs) \<and> (\<forall> y \<in> set (yCoordList xs). getY x \<le> y))"
  apply (simp)
sorry*)

(*Liste ist sortiert*)
(*lemma xCoordOrd1 : "pointList L \<Longrightarrow> last (xCoordList L) \<ge> hd (xCoordList L)"
  apply (cases L rule: xCoordList.cases)
  apply (simp add: pointList_def)
  apply (cut_tac P=L in YCoordSorted)
  apply (cut_tac P=L in XCoordSorted)
  apply (simp)
  apply (metis XCoordSorted XCoordSorted1 getX_def inInsort select_convs(1) xCoordList.simps(2))
done
  
lemma yCoordOrd1 : "pointList L \<Longrightarrow> last (yCoordList L) \<ge> hd (yCoordList L)"
  apply (cases L rule: xCoordList.cases)
  apply (simp add: pointList_def)
  apply (cut_tac P=L in YCoordSorted)
  apply (cut_tac P=L in XCoordSorted)
  apply (simp)
  apply (metis XCoordSorted XCoordSorted1 getX_def inInsort select_convs(1) xCoordList.simps(2))
done*)



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
