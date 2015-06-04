theory segmentList
imports line
begin

(*Zusätzliche Sätze die ich brauche*)
lemma inInsort : "a \<in> set (insort_insert x xs) \<longleftrightarrow> a \<in> set (xs) \<or> a = x"
  by (auto simp add: linorder_class.set_insort_insert)
theorem sortedKey : "sorted (map f (x # xs)) = (sorted (map f xs) \<and> (\<forall> y \<in> set xs. f x \<le> f y))"
  by (auto simp add: linorder_class.sorted_Cons)
lemma distinctElem : "L \<noteq> [] \<and> distinct L \<Longrightarrow> 0 \<le> i \<and> i < (size L - 1)  \<longrightarrow> (L!i) \<noteq> (L!(i+1))"
  by (auto simp add: distinct_conv_nth)



(*zusammenhängende strecken, mit mehr als 2 Ecken. jede Ecke kommt nur ein mal vor.
hat damit also nur 2 Nachbarn*)
definition pointList :: "point2d list \<Rightarrow> bool" where
"pointList L \<equiv> (size L \<ge> 3 \<and> distinct L)"

(*keine der Ecken kann sich wiederholen*)
lemma distEdge : "pointList P \<Longrightarrow> a \<in> set P \<and> b \<in> set P \<and> a \<noteq> b \<longrightarrow> \<not> pointsEqual a b"
  by (auto simp add: pointsEqual_def)

(*alle Kanten von pointList sind segmente*)
lemma pointsSegments : "pointList L \<Longrightarrow> 0 \<le> i \<and> i < (size L - 1) \<longrightarrow> segment (L!i) (L!(i+1))"
  apply (auto simp add: segment_def pointList_def pointsEqual_def)
  apply (cut_tac L=L and i=i in distinctElem, auto)
done
lemma pointsSegmentsAppend1: "pointList L \<Longrightarrow> \<forall>i<length L - 1. segment (L ! i) (L ! Suc i) \<and> segment (last L) a \<Longrightarrow>
  k < (length (L @ [a]) - 1) \<longrightarrow>  segment ((L @ [a]) ! k) ((L @ [a]) ! Suc k)"
  apply(auto)
  apply(erule_tac x="k - 1" in allE) 
  apply(erule impE)
  apply(simp add: Groups.ordered_ab_group_add_class.diff_strict_right_mono)
  apply (metis Suc_leI Suc_lessI add_2_eq_Suc' diff_0_eq_0 diff_less_mono le_numeral_Suc monoid_add_class.add.left_neutral neq0_conv not_less old.nat.distinct(2) pointList_def pred_numeral_simps(3))
  apply (auto)
  apply (metis One_nat_def Suc_leI Suc_lessI add_Suc_right diff_Suc_Suc diff_less_mono diff_zero last_conv_nth le0 length_0_conv monoid_add_class.add.right_neutral nth_append nth_append_length pointsSegments zero_less_Suc)
done
theorem pointsSegmentsAppend : "pointList L \<Longrightarrow> (\<forall> i::nat. i < (size (L @ [a]) - 1) \<longrightarrow> segment ((L @ [a])!i) ((L @ [a])!(i+1)))
  \<longleftrightarrow> (\<forall> k::nat. k < (size L - 1) \<longrightarrow> segment (L!k) (L !(k+1))) \<and> segment (last L) a"
  apply (auto)
  apply (erule_tac x="i+1" in allE)
  apply (metis One_nat_def add_Suc_right le0 monoid_add_class.add.right_neutral pointsSegments)
  apply (erule_tac x="length L - 1" in allE)
  apply (metis One_nat_def Suc_pred diff_less eq_numeral_simps(4) last_conv_nth le_0_eq length_greater_0_conv list.size(3) nth_append nth_append_length pointList_def zero_less_Suc)
  apply (simp add: pointsSegmentsAppend1)
done
 
(*keine der Kanten kann sich wiederholen*)
lemma distVertex : "pointList P \<Longrightarrow> a \<in> set P \<and> b \<in> set P \<and> c \<in> set P \<and> d \<in> set P
  \<and> a \<noteq> c \<and> a \<noteq> b \<and> c \<noteq> d \<Longrightarrow> \<not> segment_Same a b c d"  
  apply (auto)
  apply (subgoal_tac "segment a b", subgoal_tac "segment c d")
  apply (auto simp add: segment_Same_def distEdge)
  apply (auto simp add: segment_def pointsEqual_def)
done

(*Definiere ordnung von pointList nach x-Coord und nach y-Coord.*)
definition xCoordSort :: "point2d list \<Rightarrow> point2d list" where
"xCoordSort P \<equiv> sort_key (xCoord) P"
definition yCoordSort :: "point2d list \<Rightarrow> point2d list" where
"yCoordSort P \<equiv> sort_key (yCoord) P"

(*alle xCoordinaten sind in der sortierten Liste*)
lemma inXCoord : "a \<in> set xs \<longrightarrow> a \<in> set (xCoordSort xs)"
  by (auto simp add: xCoordSort_def)
lemma inYCoord : "a \<in> set xs \<longrightarrow>  a \<in> set (yCoordSort xs)"
  by (auto simp add: yCoordSort_def)
  
(*xCoordSort gibt eine sortierte Liste zurück*)
lemma xCoordSorted :  "sorted (map xCoord (xCoordSort xs))"
  by(induct xs, auto simp:sorted_insort_key xCoordSort_def)
theorem xCoordSorted1 : "sorted (map xCoord (x # xs)) \<longleftrightarrow> (sorted (map xCoord xs) \<and> (\<forall> y \<in> set xs. xCoord x \<le> xCoord y))"
  by (rule sortedKey) 
lemma yCoordSorted :  "sorted (map yCoord (yCoordSort xs))"
  by (induct xs, auto simp:sorted_insort_key yCoordSort_def)
theorem yCoordSorted1 :  "sorted (map yCoord (x # xs)) \<longleftrightarrow> (sorted (map yCoord xs) \<and> (\<forall> y \<in> set xs. yCoord x \<le> yCoord y))"
  by (rule sortedKey) 

(*erstes element der sortierten Liste ist kleiner gleich als das letzte*)
lemma xCoordOrd : "size L > 0 \<Longrightarrow> xCoord (last (xCoordSort L)) \<ge> xCoord (hd (xCoordSort L))"
  apply (cases L, simp)
  by (metis empty_iff inXCoord in_set_member last_in_set list.collapse list.set(1) member_rec(1) order_refl xCoordSorted xCoordSorted1)
lemma yCoordOrd : "size L > 0 \<Longrightarrow> yCoord (last (yCoordSort L)) \<ge> yCoord (hd (yCoordSort L))"
  apply (cases L, simp)
  by (metis empty_iff inYCoord in_set_member last_in_set list.collapse list.set(1) member_rec(1) order_refl yCoordSorted yCoordSorted1)
lemma [dest]: "pointList L \<Longrightarrow> size L > 0" by (auto simp add: pointList_def)

(*wenn eine Strecke aus der segment-Liste das Segment A B schneidet, dann schneidet auch die
Erweiterung dieser Liste das Segment A B*)
lemma listIntersectionAppend: "segment A B \<Longrightarrow>
  0 \<le> i \<and> j = i + 1 \<and> j < length L \<and> intersect (L ! i) (L ! j) A B \<Longrightarrow>
  \<exists>k l::nat. 0 \<le> k \<and> l = k + 1 \<and> l < length (a # b # L) \<and> intersect ((a # b # L) ! k) ((a # b # L) ! l) A B"
  apply (auto)
done
lemma listIntersectionDel : "segment A B \<Longrightarrow> 
\<not> intersect a b A B \<Longrightarrow> intersect ((a # b # L) ! k) ((a # b # L) ! l) A B \<longleftrightarrow> intersect (L ! i) ( L ! j) A B"
  apply (rule iffI)
  apply (cases k)
  apply (cases l)
  apply (auto)
  apply (subst intersect_def) apply (auto)
sorry
theorem listIntersection : "segment A B \<Longrightarrow>
  intersect ((a # b # L) ! k) ((a # b # L) ! l) A B \<longleftrightarrow> (intersect a b A B \<or> intersect ( L ! (k - 2)) ( L ! (l - 2)) A B)"
  apply (rule iffI)
  apply (cases "intersect a b A B", simp)
  apply (rule disjI2)
  apply (cut_tac A=A and B=B and L=L and a=a and b=b and k=k and l=l and i="k - 2" and j="l - 2"  in listIntersectionDel)
  apply (assumption+, simp)
  apply (erule disjE)
  apply (cut_tac L="[a, b]" and A=A and B=B and a=a and b=b and i=0 and j=1 in listIntersectionAppend)
  apply (assumption, simp)
  apply ((erule exE)+, (erule conjE)+, safe)
  apply (metis drop_1_Cons listIntersectionDel nth_via_drop)
  by (metis drop_1_Cons listIntersectionDel nth_via_drop)

(*lemma listIntersection: "segment A B \<Longrightarrow>
  \<exists>i j. 0 \<le> i \<and> j = i + 1 \<and> j < length L \<longrightarrow> intersect (L ! 0) (L ! j) A B \<Longrightarrow>
  \<exists>k l. 0 \<le> k \<and> l = k + 1 \<and> l < length L \<longrightarrow> intersect ((a # b # L) ! 10) ((a # b # L) ! 8) A B"
  by (cases L, auto)
lemma listIntersection1: "segment A B \<Longrightarrow>
  \<exists>i j. 0 \<le> i \<and> j = i + 1 \<and> j < length L \<and> intersect (L ! 1) (L ! j) A B \<Longrightarrow>
  \<exists>k l. 0 \<le> k \<and> l = k + 1 \<and> l < length L + 2 \<longrightarrow> intersect ((a # b # L) ! 10) ((a # b # L) ! 20) A B"
  by (erule exE, rule_tac x="k + 2" in exI, auto)*)





(*alte Definition*)

(*brauche ich die equivalente beschreibung mit insort_key noch?*)
(*fun xCoordSort :: "point2d list \<Rightarrow> point2d list" where
  "xCoordSort [] = []"
  | "xCoordSort (x#xs) = insort_key xCoord x (xCoordSort xs)" 
fun yCoordSort :: "point2d list \<Rightarrow> point2d list" where
  "yCoordSort [] = []"
  | "yCoordSort (x#xs) = insort_key yCoord x (yCoordSort xs)" 
lemma xCoordSort_right : "xCoordSort P = xCoordSort P"
  apply (simp add: xCoordSort_def)
  apply (induction P rule: xCoordSort.induct, simp)
  apply (simp)
done
lemma yCoordSort_right : "yCoordSort P = yCoordSort P"
  apply (simp add: yCoordSort_def)
  apply (induction P rule: yCoordSort.induct, simp)
  apply (simp)
done*)

(*for trapezoidalmap. Sollte noch mit Lambda abstrakter definiert werden*)
(*insort_insert damit neue Liste distinct ist*)
(*fun yCoordList ::  "point2d list \<Rightarrow> real list" where
"yCoordList [] = []" 
| "yCoordList (x#xs) = insort_insert (yCoord x) (yCoordList xs)"
fun xCoordList ::  "point2d list \<Rightarrow> real list" where
"xCoordList [] = []" 
| "xCoordList (x#xs) = insort_insert (xCoord x) (xCoordList xs)"*)

(*xCoordList gibt eine sortierte Liste zurück*)
(*lemma XCoordSort : "sorted (xCoordList P)"
  apply (induct P rule: xCoordList.induct, simp)
  apply (simp add: sorted_insort_insert)
done
lemma YCoordSort : "sorted (yCoordList P)"
  apply (induct P rule: yCoordList.induct, simp)
  apply (simp add: sorted_insort_insert)
done*)

(*alle xCoordinaten sind in der neuen Liste*)
(*lemma inXCoord : "a \<in> set xs \<longrightarrow> (xCoord a) \<in> set (xCoordList xs)"
  apply (rule impI)
  apply (induct xs rule: yCoordList.induct, simp)
  apply (simp, erule disjE, simp)
  apply (simp add: inInsort)
  apply (simp add: inInsort)
done
lemma inYCoord : "a \<in> set xs \<longrightarrow> (yCoord a) \<in> set (yCoordList xs)"
  apply (rule impI)
  apply (induct xs rule: xCoordList.induct, simp)
  apply (simp, erule disjE, simp)
  apply (simp add: inInsort)
  apply (simp add: inInsort)
done*)
(*xCoordList gibt eine sortierte Liste zurück*)
(*theorem XCoordSort1 : "sorted (xCoordList (x # xs)) = (sorted (xCoordList xs) \<and> (\<forall> y \<in> set (xCoordList xs). xCoord x \<le> y))"
  apply (auto)
  apply (simp add: XCoordSort)
sorry
theorem YCoordSort1 : "sorted (yCoordList (x # xs)) = (sorted (yCoordList xs) \<and> (\<forall> y \<in> set (yCoordList xs). yCoord x \<le> y))"
  apply (simp)
sorry*)

(*Liste ist sortiert*)
(*lemma xCoordOrd1 : "pointList L \<Longrightarrow> last (xCoordList L) \<ge> hd (xCoordList L)"
  apply (cases L rule: xCoordList.cases)
  apply (simp add: pointList_def)
  apply (cut_tac P=L in YCoordSort)
  apply (cut_tac P=L in XCoordSort)
  apply (simp)
  apply (metis XCoordSort XCoordSort1 xCoord_def inInsort select_convs(1) xCoordList.simps(2))
done
  
lemma yCoordOrd1 : "pointList L \<Longrightarrow> last (yCoordList L) \<ge> hd (yCoordList L)"
  apply (cases L rule: xCoordList.cases)
  apply (simp add: pointList_def)
  apply (cut_tac P=L in YCoordSort)
  apply (cut_tac P=L in XCoordSort)
  apply (simp)
  apply (metis XCoordSort XCoordSort1 xCoord_def inInsort select_convs(1) xCoordList.simps(2))
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
