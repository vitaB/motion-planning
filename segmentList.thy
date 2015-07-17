theory segmentList
imports line
begin

(*Zusätzliche Sätze die ich brauche*)
lemma distinctElem : "L \<noteq> [] \<and> distinct L \<Longrightarrow> i < (size L - 1) \<Longrightarrow> (L!i) \<noteq> (L! Suc i)"
  by (auto simp add: distinct_conv_nth)
lemma intersectNext: "length L \<ge> 1 \<Longrightarrow> \<not> intersect b (hd L) A B \<Longrightarrow> intersect ((b # L) ! k) ((b # L) ! Suc k) A B \<Longrightarrow>
  intersect (L ! (k - 1)) (L ! (Suc k - 1)) A B"
  apply (cases "k = 0", simp) apply (metis Suc_n_not_le_n hd_conv_nth length_0_conv, auto)
done

(*zusammenhängende strecken, mit mehr als 2 Ecken. jede Ecke kommt nur ein mal vor.
hat damit also nur 2 Nachbarn*)
definition pointList :: "point2d list \<Rightarrow> bool" where
"pointList L \<equiv> (size L \<ge> 3 \<and> distinct L)"
definition pointListSeg :: "point2d list \<Rightarrow> (point2d*point2d) \<Rightarrow> bool" where
  "pointList L \<Longrightarrow> pointListSeg L S \<equiv> \<exists> i < length L - 1. L!i = fst S \<and> L!i = snd S"
definition pointLists :: "(point2d list) list \<Rightarrow> bool" where "pointLists PL \<equiv> \<forall> i < length PL. pointList (PL!i)"
definition pointlistsSeg :: "(point2d list) list \<Rightarrow> (point2d*point2d) \<Rightarrow> bool" where
  "pointLists PL \<Longrightarrow> pointlistsSeg PL S \<equiv> \<exists> i < length PL. pointListSeg (PL!i) S"
lemma [simp]: "pointList L \<Longrightarrow> size L > 0" by (auto simp add: pointList_def)
lemma pointListRev[simp] : "pointList L \<Longrightarrow> pointList (rev L)" by (simp add: pointList_def)

(*keine der Ecken kann sich wiederholen*)
lemma distEdge : "pointList P \<Longrightarrow> a \<in> set P \<and> b \<in> set P \<and> a \<noteq> b \<longrightarrow> \<not> pointsEqual a b"
  by (metis pointsEqual1)
lemma distEdge1 : "pointList L \<Longrightarrow> i < size L \<Longrightarrow> k < size L \<Longrightarrow> k \<noteq> i \<Longrightarrow> \<not> pointsEqual (L ! i) (L ! k)"
  by (auto simp add: pointList_def distinct_conv_nth)
   
(*keine der Kanten kann sich wiederholen*)
lemma distVertex : "pointList P \<Longrightarrow> a \<in> set P \<and> b \<in> set P \<and> c \<in> set P \<and> d \<in> set P
  \<and> a \<noteq> c \<and> a \<noteq> b \<and> c \<noteq> d \<Longrightarrow> \<not> segment_Same a b c d"  
  apply (auto, subgoal_tac "segment a b", subgoal_tac "segment c d")
  apply (auto simp add: segment_Same_def distEdge segment_def pointsEqual_def)
done

(*alle Kanten von pointList sind segmente*)
lemma pointsSegments: "pointList L \<Longrightarrow> 0 \<le> i \<and> i < (size L - 1) \<Longrightarrow> segment (L!i) (L! Suc i)"
  apply (auto simp add: segment_def pointList_def pointsEqual_def)
  apply (cut_tac L=L and i=i in distinctElem, auto)
done

(*wenn man pointList um ein segment erweitert, sind alle Elemente der neuen Liste auch segmente*)
lemma pointsSegmentsAppend1: "pointList L \<Longrightarrow> segment (last L) a \<Longrightarrow>
  k < (length (L @ [a]) - 1) \<Longrightarrow> segment ((L @ [a]) ! k) ((L @ [a]) ! Suc k)"
  apply (auto)
  apply (metis One_nat_def Suc_leI Suc_lessI diff_Suc_Suc diff_less_mono diff_zero last_conv_nth le0 length_0_conv nth_append nth_append_length pointsSegments zero_less_Suc)
done
lemma pointsSegmentsAppend2: "length L \<ge> 1 \<Longrightarrow> \<forall>i < length L. segment ((L @ [a]) ! i) ((L @ [a]) ! Suc i)
  \<Longrightarrow> segment (last L) a"
  apply (erule_tac x="length L - 1" in allE)
  apply (simp)
  apply (auto simp add: nth_append)
  apply (smt2 Suc_eq_plus1 Suc_pred add.commute diff_self_eq_0 last_conv_nth le_Suc_ex less_not_refl list.size(3) monoid_add_class.add.left_neutral neq0_conv nth_Cons_0 old.nat.distinct(2))
done
theorem pointsSegmentsAppend: "pointList L \<Longrightarrow> k < size L - 1 \<Longrightarrow> (\<forall>i < (size (L @ [a]) - 1). segment ((L @ [a])!i) ((L @ [a])! Suc i))
  = (segment (L!k) (L ! Suc k) \<and> segment (last L) a)"
  apply (rule iffI) 
  apply (rule conjI)
  apply (simp add: pointsSegments)
  apply (simp add: pointsSegmentsAppend2)
by (metis pointsSegmentsAppend1)


(*Definiere ordnung von pointList nach x-Coord und nach y-Coord.
 Nötig um zusagen welcher Punkt auf der x und y achse ganz rechts/links/unten/oben ist*)
definition xCoordSort :: "point2d list \<Rightarrow> point2d list" where
"xCoordSort P \<equiv> sort_key (xCoord) P"
definition yCoordSort :: "point2d list \<Rightarrow> point2d list" where
"yCoordSort P \<equiv> sort_key (yCoord) P"
(*Zusätzliche Lemmas die ich brauche*)
lemma inInsort : "a \<in> set (insort_insert x xs) \<longleftrightarrow> a \<in> set (xs) \<or> a = x"
  by (auto simp add: linorder_class.set_insort_insert)
theorem sortedKey : "sorted (map f (x # xs)) = (sorted (map f xs) \<and> (\<forall> y \<in> set xs. f x \<le> f y))"
  by (auto simp add: linorder_class.sorted_Cons)
(*alle punkte sind nach dem sortieren noch da*)
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


(*3 beliebige Ecken in der pointList sind kolliniear*)
(*mit der negation, brauche ich evtl. die Definition von pointList nicht mehr*)
definition collinearList :: "point2d list \<Rightarrow> bool" where
  "collinearList L \<equiv> (\<exists> a b c. a < length L \<and> b < length L \<and> c < length L \<and>
  a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c \<and> collinear (L!a) (L!b) (L!c))"
lemma collinearList1 : "collinear a b c = collinearList [a,b,c]"
  apply (simp add: collinearList_def, rule iffI)
  apply (rule_tac  x=0 in exI, simp, rule_tac  x=1 in exI, simp, rule_tac  x=2 in exI, simp)
  apply (safe)
oops
lemma collinearList2: "\<not>collinearList (a#xs) \<Longrightarrow> \<not>collinearList (xs)"
  apply (simp add: collinearList_def, safe)
  apply (erule_tac x="aa+1" in allE, simp)
  apply (erule_tac x="b+1" in allE, simp)
  apply (erule_tac x="c+1" in allE, simp)
done
lemma collinearListRev: "collinearList xs = collinearList (rev xs)"
  apply (simp add: collinearList_def, rule iffI, safe)
  apply (rule_tac x="(length xs - 1) - a" in exI, safe, simp)
  apply(rule_tac x="(length xs - 1) - b" in exI, safe, simp)
  apply(rule_tac x="(length xs - 1) - c" in exI, safe, simp)
  apply(simp add: rev_nth)+
  apply(rule_tac x="(length xs - 1) - a" in exI, safe, simp)
  apply(rule_tac x="(length xs - 1) - b" in exI, safe, simp)
  apply(rule_tac x="(length xs - 1) - c" in exI, safe, simp)
  apply(simp add: rev_nth)+
done

(*collineare Liste erweitert*)
lemma collinearListAppend1 [simp]: "collinearList xs \<Longrightarrow> collinearList (a#xs)"
  by (metis collinearList2)
lemma collinearListAppend2 [simp]: "collinearList xs \<Longrightarrow> collinearList (xs @ [a])"
  by (metis collinearList2 collinearListRev rev.simps(2) rev_rev_ident)
theorem collinearListAppend [simp]: "collinearList xs \<Longrightarrow> collinearList (x @ xs)"
oops

(*keine 3 Ecken hintereinander sind collinear, wenn \<not>collinearList L*)
lemma collinearListAdj: "\<not>collinearList L \<Longrightarrow> a < length L - 2 \<Longrightarrow> \<not>collinear (L ! a)(L! Suc a)(L! Suc(Suc a))"
  apply (simp add: collinearList_def)
  apply (erule_tac x=a in allE, safe)
  apply (metis diff_less_Suc lessI less_trans_Suc lift_Suc_mono_less_iff)
  apply (erule_tac x="Suc a" in allE, safe)
  apply (metis Suc_lessD add_2_eq_Suc' less_diff_conv)
  apply (erule_tac x="Suc (Suc a)" in allE, safe)
  apply (simp add: less_diff_conv n_not_Suc_n)+
done

(*der punkt P befindet sich collinear mit irgendwelchen der segmente von L*)
definition collinearListPoint :: "point2d list \<Rightarrow> point2d \<Rightarrow> bool" where
  "collinearListPoint L p \<equiv> \<exists> a. a < length L - 1 \<and> collinear (L!a) (L!Suc a) p"


(*keiner der Strecken aus der pointList schneidet sich (echt) mit einer anderen Strecke der pointList*)
definition crossingFreePList :: "point2d list \<Rightarrow> bool" where
 "crossingFreePList P \<equiv> \<forall>i k. ((k < length P - 1 \<and> i < length P - 1) \<longrightarrow>
 \<not>crossing (P ! i) (P ! Suc i) (P ! k) (P ! Suc k))"

(*keiner der Strecken aus der pointList überschneidet sich mit einer anderen Strecke der pointList
  (außer natürlich die jeweiligen Nachbarkanten)*)
definition intersectionFreePList :: "point2d list \<Rightarrow> bool" where
 "intersectionFreePList P \<equiv> \<forall>i k. ((k < length P - 1 \<and> i < length P - 1 \<and> (P!i) \<noteq> (P!k) \<and> (P ! i) \<noteq> (P ! Suc k)
 \<and> (P ! Suc i) \<noteq> (P ! k)) \<longrightarrow> \<not>intersect (P ! i) (P ! Suc i) (P ! k) (P ! Suc k))"

(*wenn an der ersten stelle keine intersection, dann an der zweiten Stelle*)
lemma sizeOfList : "\<not> intersect a b A B \<Longrightarrow> intersect ((a # b # L) ! k) ((a # b # L) ! Suc k) A B \<Longrightarrow> k \<ge> 1"
  by (cases k, auto)
lemma listIntersectNth: "\<not> intersect a b A B \<Longrightarrow> intersect ((a # b # L) ! i) ((a # b # L) ! Suc i) A B \<Longrightarrow>
  intersect ((b # L) ! (i - 1)) ((b # L) ! (Suc i - 1)) A B"
  by (cut_tac A=A and B=B and a=a and b=b and L=L and k=i in sizeOfList, auto)

(*wenn eine Strecke aus der segment-Liste das Segment A B schneidet, dann schneidet auch die
Erweiterung dieser Liste das Segment A B*)
lemma listIntersectionAppend: "segment A B \<Longrightarrow>
  i < length L - 1 \<Longrightarrow> intersect (L ! i) (L ! Suc i) A B \<Longrightarrow>
  \<exists>k l::nat. 0 \<le> k \<and> l = k + 1 \<and> l < length (a # b # L) \<and> intersect ((a # b # L) ! k) ((a # b # L) ! l) A B"
  by (rule_tac x="i + 2" in exI, rule_tac x="i + 3" in exI, auto)
lemma listIntersectionDel : "segment A B \<Longrightarrow> length L \<ge> 1 \<Longrightarrow> \<not> intersect a b A B \<Longrightarrow>
  (\<exists> k::nat. k \<ge> 0 \<and> (k + 1) < length (a # b # L) \<and> intersect ((a # b # L) ! k) ((a # b # L) ! (k + 1)) A B)
  \<longleftrightarrow> ((\<exists> i::nat. i \<ge> 0 \<and> i + 1 < length L \<and> intersect (L ! i) ( L ! (i + 1)) A B) \<or> intersect b (hd L) A B)"
  apply (auto)
  apply (rule_tac x="k - 2" in exI)
  apply (subgoal_tac "k \<ge> 2")
  apply (auto)
  apply (subgoal_tac "Suc (k - 2) = k - 1 \<and> (k - 2) = k - Suc (Suc 0)")
  apply (auto)
  apply (metis One_nat_def Suc_1 hd_conv_nth le_0_eq le_Suc_eq length_0_conv not_less_eq_eq nth_Cons_0 nth_Cons_Suc)
  apply (rule_tac x="1" in exI, auto)
  apply (subgoal_tac "L ! 0 = hd L")
by (auto, metis Suc_n_not_le_n gen_length_code(1) hd_conv_nth length_code)
lemma listIntersection1 : "segment A B \<Longrightarrow> length L \<ge> 1 \<Longrightarrow> \<not> intersect a b A B \<Longrightarrow>
  (intersect ((a # b # L) ! (k)) ((a # b # L) ! (k + 1)) A B \<longleftrightarrow> ( k\<ge>2 \<and> intersect (L ! (k - 2)) ( L ! (k - 1)) A B)) \<or> intersect b (hd L) A B"
  apply (safe)
  apply (metis (erased, hide_lams) Suc_eq_plus1 add.commute add_leE hd_conv_nth le_antisym list.size(3) monoid_add_class.add.right_neutral not_less_eq_eq nth_Cons_0 nth_Cons_Suc one_add_one)
  apply (subgoal_tac "k \<ge> 2")
  apply (subgoal_tac "(k - Suc (Suc 0)) = k - 2")
  apply (simp, simp, simp)
  apply (metis One_nat_def Suc_1 hd_conv_nth le_0_eq le_Suc_eq length_0_conv not_less_eq_eq nth_Cons_0 nth_Cons_Suc)
  apply (subgoal_tac "(k - Suc (Suc 0)) = k - 2")
  apply (auto)
done
theorem listIntersection : "segment A B \<Longrightarrow> length L \<ge> 1 \<Longrightarrow>
  intersect ((a # b # L) ! k) ((a # b # L) ! Suc k) A B \<longleftrightarrow>
  ((k = 0 \<and> intersect a b A B) \<or> (k = 1 \<and> intersect b (hd L) A B)) \<or> (k\<ge>2 \<and> intersect ( L ! (k - 2)) ( L ! (k - 1)) A B)"
  apply (safe)
  apply (simp, simp)
  apply (metis less_2_cases not_less nth_Cons_0)
  apply (simp)
  apply (metis One_nat_def diff_self_eq_0 hd_conv_nth le_imp_less_Suc length_0_conv less_2_cases less_imp_le_nat not_less nth_Cons')
  apply (metis One_nat_def Suc_eq_plus1 listIntersection1 nth_Cons_Suc)
  apply (simp)
  apply (metis Suc_1 diff_0_eq_0 diff_Suc_eq_diff_pred diff_self_eq_0 diffs0_imp_equal nth_Cons' old.nat.exhaust)
  apply (simp) apply (metis One_nat_def Suc_1 Suc_pred diff_Suc_eq_diff_pred neq0_conv nth_Cons')
  apply (metis Suc_1 diff_Suc_1 diff_Suc_eq_diff_pred intersectNext nth_Cons' nth_Cons_Suc)
  apply (metis Suc_eq_plus1 listIntersection1)
  apply (simp, simp)
  apply (metis One_nat_def hd_conv_nth list.size(3) not_one_le_zero)
  by (simp, metis One_nat_def Suc_1)





(*alte Definition*)
(*wie kann man nth als prädikat darstellen? *)
(*lemma sizeOfList : "intersect (L ! k) (L !(k + 1)) A B \<Longrightarrow> length L > k"
  apply (cases k, auto) apply (rule classical)
oops*)
(*value " 0 - 2::nat" funktioniert nur wenn man numeral verwendet! nth_Cons_numeral*)
(*lemma intersectNext2: "length L \<ge> 1 \<Longrightarrow> intersect (L ! (k - 1)) (L ! Suc (k - 1)) A B \<Longrightarrow> k \<ge> 1" 
  apply (auto)
  apply (cases k, simp)
oops*)
(*lemma intersectNext5: "length L \<ge> 1 \<Longrightarrow> \<not> intersect b (hd L) A B \<Longrightarrow>
  intersect ((b # L) ! numeral k) ((b # L) ! (numeral k + 1)) A B = intersect (L ! (numeral k - 1)) (L ! Suc (numeral k - 1)) A B"
  apply (rule iffI)
  apply (metis Suc_eq_plus1 Suc_numeral diff_Suc_1 nth_Cons_numeral numeral_eq_Suc)
by (metis Suc_eq_plus1_left add.commute add_diff_cancel_left' nth_Cons' numeral_eq_Suc old.nat.distinct(2))*)
(*lemma listIntersectNth1 [simp]: "\<not> intersect a b A B \<Longrightarrow> intersect ((a # b # L) ! i) ((a # b # L) ! Suc i) A B =
  intersect ((b # L) ! (i - 1)) ((b # L) ! (Suc i - 1)) A B"
  apply (auto, subgoal_tac " i \<ge> 1", simp, metis Suc_eq_plus1 nth_Cons_Suc sizeOfList1)
  apply (subgoal_tac " i \<ge> 1", simp)
*)

(*
lemma pointsSegmentsAppend1: "pointList L \<Longrightarrow> \<forall>i<length L - 1. segment (L ! i) (L ! Suc i) \<and> segment (last L) a \<Longrightarrow>
  k < (length (L @ [a]) - 1) \<Longrightarrow> segment ((L @ [a]) ! k) ((L @ [a]) ! Suc k)"
  apply(auto)
  apply(erule_tac x="k - 1" in allE) 
  apply(erule impE)
  apply(simp add: Groups.ordered_ab_group_add_class.diff_strict_right_mono)
  apply (metis Suc_leI Suc_lessI add_2_eq_Suc' diff_0_eq_0 diff_less_mono le_numeral_Suc monoid_add_class.add.left_neutral neq0_conv not_less old.nat.distinct(2) pointList_def pred_numeral_simps(3))
  apply (auto)
  apply (metis One_nat_def Suc_leI Suc_lessI add_Suc_right diff_Suc_Suc diff_less_mono diff_zero last_conv_nth le0 length_0_conv monoid_add_class.add.right_neutral nth_append nth_append_length pointsSegments zero_less_Suc)
done
theorem pointsSegmentsAppend : "pointList L \<Longrightarrow> (\<forall> i::nat. i < (size (L @ [a]) - 1) \<longrightarrow> segment ((L @ [a])!i) ((L @ [a])!(i+1)))
  = ((\<forall> k::nat. k < (size L - 1) \<longrightarrow> segment (L!k) (L !(k+1))) \<and> segment (last L) a)"
  apply (auto simp add: pointsSegmentsAppend1)
  apply (erule_tac x="i+1" in allE)
  apply (metis One_nat_def add_Suc_right le0 monoid_add_class.add.right_neutral pointsSegments)
  apply (erule_tac x="length L - 1" in allE)
  apply (metis One_nat_def Suc_pred diff_less eq_numeral_simps(4) last_conv_nth le_0_eq length_greater_0_conv list.size(3) nth_append nth_append_length pointList_def zero_less_Suc)
done*)
end
