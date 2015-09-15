theory segmentList
imports segment
begin

(*additional lemmas*)
lemma distinctElem : "L \<noteq> [] \<and> distinct L \<Longrightarrow> i < (size L - 1) \<Longrightarrow> (L!i) \<noteq> (L! Suc i)"
  by (auto simp add: distinct_conv_nth)
lemma intersectNext: "length L \<ge> 1 \<Longrightarrow> \<not> intersect b (hd L) A B \<Longrightarrow>
  intersect ((b # L) ! k) ((b # L) ! Suc k) A B \<Longrightarrow> intersect (L ! (k - 1)) (L ! (Suc k - 1)) A B"
  by (cases "k = 0", simp, metis Suc_n_not_le_n hd_conv_nth length_0_conv, auto)
lemma inInsort : "a \<in> set (insort_insert x xs) \<longleftrightarrow> a \<in> set (xs) \<or> a = x"
  by (auto simp add: linorder_class.set_insort_insert)
theorem sortedKey : "sorted (map f (x # xs)) = (sorted (map f xs) \<and> (\<forall> y \<in> set xs. f x \<le> f y))"
  by (auto simp add: linorder_class.sorted_Cons)

(*connected edges, with more than 2 corners.
every corner is found only one time. So therefore has only 2 neighbors*)
definition pointList :: "point2d list \<Rightarrow> bool" where
"pointList L \<equiv> (size L \<ge> 3 \<and> distinct L)"
lemma pointListNotEmpty[dest]: "pointList [] \<Longrightarrow> False" by (simp add: pointList_def)
lemma pointListRev[simp] : "pointList L \<Longrightarrow> pointList (rev L)" by (simp add: pointList_def)
(*List with pointList's*)
definition pointLists :: "(point2d list) list \<Rightarrow> bool" where
  "pointLists PL \<equiv> length PL > 0 \<and> (\<forall>  i < length PL. pointList (PL!i))"
lemma pointListsEmpty[dest]: "pointLists ([] # PL) \<Longrightarrow> False"
  by (auto simp add: pointLists_def pointList_def)
lemma pointListsSimp : "(pointList A \<and> pointList B) \<longleftrightarrow> pointLists [A,B]"
  by (auto simp add: pointLists_def, case_tac i, auto)
lemma pointListsSimp1 : "pointLists [A] = pointList A" by(simp add: pointLists_def)
(*jedes Element ist eine pointList*)
lemma pointListsSimp2 [simp]: "i < length PL \<Longrightarrow> pointLists PL \<Longrightarrow> pointList (PL!i)"
  by (auto simp add: pointLists_def)

(*is a segment in the pointList?*)
definition segInPointList :: "point2d list \<Rightarrow> (point2d*point2d) \<Rightarrow> bool" where
  "pointList L \<Longrightarrow> segInPointList L S \<equiv> \<exists> i < length L - 1. L!i = fst S \<and> L!i = snd S"
(*is a segment in the pointList-List?*)
definition segInPointLists :: "(point2d list) list \<Rightarrow> (point2d*point2d) \<Rightarrow> bool" where
  "pointLists PL \<Longrightarrow> segInPointLists PL S \<equiv> \<exists> i < length PL. segInPointList (PL!i) S"

(*none of the corners can be repeated*)
lemma distVertex : "pointList L \<Longrightarrow> i < size L \<Longrightarrow> k < size L \<Longrightarrow> k \<noteq> i
  \<Longrightarrow> pointsEqual (L ! i) (L ! k) \<Longrightarrow> False"
  by (metis nth_eq_iff_index_eq pointList_def pointsEqual1)
(*none of the edges can be repeated*)
lemma distEdge : "pointList L \<Longrightarrow> a < size L \<Longrightarrow> b < size L \<Longrightarrow> c < size L \<Longrightarrow> d < size L \<Longrightarrow>
   a \<noteq> c \<and> a \<noteq> b \<and> c \<noteq> d \<Longrightarrow> segment_Same (L!a) (L!b) (L!c) (L!d) \<Longrightarrow> False"  
  apply (subgoal_tac "segment (L!a) (L!b) \<and> segment (L!c) (L!d)", auto)
by (auto simp add: segment_Same_def distVertex segment_def nth_eq_iff_index_eq pointList_def)


(*there is no point in the point list, with the same xCoordinate*)
definition uniqueXCoord :: "point2d list \<Rightarrow> bool" where
  "uniqueXCoord L \<equiv> \<forall> a b. a \<noteq> b \<longrightarrow> xCoord (L!a) \<noteq> xCoord (L!b)"
lemma uniqueXCoordPointList: "3 \<le> length L \<Longrightarrow> uniqueXCoord L \<Longrightarrow> pointList (L)"
  by (simp add: uniqueXCoord_def pointList_def, metis distinct_conv_nth)


(*all edges of pointList are segments*)
lemma pointsSegments: "pointList L \<Longrightarrow> 0 \<le> i \<Longrightarrow> i < (size L - 1) \<Longrightarrow> segment (L!i) (L! Suc i)"
  apply (auto simp add: segment_def pointList_def pointsEqual_def)
by (cut_tac L=L and i=i in distinctElem, auto)

(*if you extend pointsList by one segment, all elements of the new list are also segments*)
lemma pointsSegmentsAppend1: "pointList L \<Longrightarrow> segment (last L) a \<Longrightarrow> k < (length (L @ [a]) - 1) \<Longrightarrow>
  segment ((L @ [a]) ! k) ((L @ [a]) ! Suc k)"
  by (auto, metis One_nat_def Suc_leI Suc_lessI diff_Suc_Suc diff_less_mono diff_zero
    last_conv_nth le0 length_0_conv nth_append nth_append_length pointsSegments zero_less_Suc)
lemma pointsSegmentsAppend2: "length L \<ge> 1 \<Longrightarrow> \<forall>i < length L. segment ((L@[a])!i) ((L@[a]) ! Suc i)
  \<Longrightarrow> segment (last L) a"
  apply (erule_tac x="length L - 1" in allE, auto simp add: nth_append)
  by (smt Suc_eq_plus1 Suc_pred add.commute diff_self_eq_0 last_conv_nth le_Suc_ex less_not_refl
    list.size(3) monoid_add_class.add.left_neutral neq0_conv nth_Cons_0 old.nat.distinct(2))
theorem pointsSegmentsAppend: "pointList L \<Longrightarrow> k < size L - 1 \<Longrightarrow>
  (\<forall>i < (size (L @ [a]) - 1). segment ((L @ [a])!i) ((L @ [a])! Suc i))
  = (segment (L!k) (L ! Suc k) \<and> segment (last L) a)"
  apply (safe, simp add: pointsSegments, simp add: pointsSegmentsAppend2)
by (metis pointsSegmentsAppend1)


(*Define order of point list after x-Coord and after x-Coord.
  Needed to say which point on the X and Y axes is far right/left/top/bottom*)
definition xCoordSort :: "point2d list \<Rightarrow> point2d list" where
"xCoordSort P \<equiv> sort_key (xCoord) P"
definition yCoordSort :: "point2d list \<Rightarrow> point2d list" where
"yCoordSort P \<equiv> sort_key (yCoord) P"
(*x/y-Sort gibt returns a sorted list*)
lemma xCoordSorted :  "sorted (map xCoord (xCoordSort xs))"
  by(induct xs, auto simp:sorted_insort_key xCoordSort_def)
theorem xCoordSorted1 : "sorted (map xCoord (x # xs)) \<longleftrightarrow>
    (sorted (map xCoord xs) \<and> (\<forall> y \<in> set xs. xCoord x \<le> xCoord y))"
  by (rule sortedKey) 
lemma yCoordSorted :  "sorted (map yCoord (yCoordSort xs))"
  by (induct xs, auto simp:sorted_insort_key yCoordSort_def)
theorem yCoordSorted1 :  "sorted (map yCoord (x # xs)) \<longleftrightarrow>
    (sorted (map yCoord xs) \<and> (\<forall> y \<in> set xs. yCoord x \<le> yCoord y))"
  by (rule sortedKey) 
(*All the points in the list are still there after sort*)
lemma inXCoord : "a \<in> set xs \<longrightarrow> a \<in> set (xCoordSort xs)"
  by (auto simp add: xCoordSort_def)
lemma inYCoord : "a \<in> set xs \<longrightarrow>  a \<in> set (yCoordSort xs)"
  by (auto simp add: yCoordSort_def)

(*first element of the sorted list is less or equal than the last.*)
lemma xCoordOrd : "size L > 0 \<Longrightarrow> xCoord (last (xCoordSort L)) \<ge> xCoord (hd (xCoordSort L))"
  apply (cases L, simp, insert inXCoord xCoordSorted xCoordSorted1)
  by (metis empty_iff in_set_member last_in_set list.collapse list.set(1) member_rec(1) order_refl)
lemma yCoordOrd : "size L > 0 \<Longrightarrow> yCoord (last (yCoordSort L)) \<ge> yCoord (hd (yCoordSort L))"
  apply (cases L, simp, insert inYCoord yCoordSorted yCoordSorted1)
  by (metis empty_iff in_set_member last_in_set list.collapse list.set(1) member_rec(1) order_refl)


(*any 3 corners in the point list are collinear.*)
definition collinearList :: "point2d list \<Rightarrow> bool" where
  "collinearList L \<equiv> (\<exists> a b c. a < length L \<and> b < length L \<and> c < length L \<and>
  a\<noteq>b \<and> a\<noteq>c \<and> b\<noteq>c \<and> collinear (L!a) (L!b) (L!c))"
lemma collinearListThree[simp]: "length L = 3 \<Longrightarrow> collinearList L = collinear (L!0) (L!1) (L!2)"
  apply (auto simp add: collinearList_def)
  apply (case_tac "a=0", case_tac "b=1", subgoal_tac "c=2", auto)
    apply (case_tac "b=2", subgoal_tac "c=1", auto)
  apply (case_tac "a=1", case_tac "b=0", subgoal_tac "c=2", auto)
    apply (simp add: less_Suc_eq numeral_2_eq_2 numeral_3_eq_3)
  apply (case_tac "b=0", subgoal_tac "c=1", auto)
    apply (simp add: less_Suc_eq numeral_2_eq_2 numeral_3_eq_3)
  apply (subgoal_tac "b=1", subgoal_tac "c=0", auto)
    apply (simp add: less_Suc_eq numeral_2_eq_2 numeral_3_eq_3)
  apply (rule_tac x=0 in exI, simp, rule_tac x=1 in exI, simp, rule_tac x=2 in exI, simp)
done    
lemma collinearListLength[dest]: "length L < 3 \<Longrightarrow> collinearList L \<Longrightarrow> False"
  apply (simp add: collinearList_def, safe)
  apply (case_tac "a=0", subgoal_tac "b = 1", simp)
    using numeral_3_eq_3 apply linarith
  apply (subgoal_tac "b = 0", simp)
  using numeral_3_eq_3 apply linarith
done
lemma collinearListNoPointsEq: "length L \<ge> 3 \<Longrightarrow> \<not>collinearList L \<Longrightarrow> i < size L \<Longrightarrow> k < size L
  \<Longrightarrow> k \<noteq> i \<Longrightarrow> \<not>pointsEqual (L ! i) (L ! k)"
  apply (auto simp add: collinearList_def)
  apply (erule_tac x=i in allE, simp, erule_tac x=k in allE, safe)
  apply (case_tac "k=0")
    apply (case_tac "i = 1")
    apply (erule_tac x=2 in allE, simp)
    apply (subgoal_tac "i = 2")
    apply (erule_tac x=1 in allE, simp)
    apply (rule ccontr, erule_tac x=2 in allE, simp)
  apply (case_tac "i=0")
    apply (case_tac "k=1")
    apply (erule_tac x=2 in allE, simp)
    apply (erule_tac x=1 in allE, simp)
  apply (erule_tac x=0 in allE, simp)
done
(*mit der negation, brauche ich evtl. die Definition von pointList nicht mehr*)
lemma collinearPointList: "3 \<le> length L \<Longrightarrow> \<not>collinearList L \<Longrightarrow> pointList L"
  apply (simp add: pointList_def collinearList_def)
  apply (subgoal_tac "\<forall> i k. i < size L \<and> k < size L \<and> k \<noteq> i \<longrightarrow> \<not>pointsEqual (L ! i) (L ! k)")
  apply (simp add: distinct_conv_nth)
using collinearListNoPointsEq collinearList_def by auto

lemma collinearList1: "collinear a b c = collinearList [a,b,c]"
  apply (simp add: collinearList_def, rule iffI)
  apply (rule_tac  x=0 in exI, simp, rule_tac  x=1 in exI, simp, rule_tac  x=2 in exI, simp, safe)
  apply (case_tac "aa = 0", subgoal_tac "ba > 0", case_tac "ba = 1", subgoal_tac "ca = 2", simp+)
  apply (case_tac "ba = 0", case_tac "aa = 1", subgoal_tac "ca = 2", simp+)
by (subgoal_tac "ca = 0", case_tac "aa = 1", subgoal_tac "ba = 2", simp+)
lemma collinearList2: "\<not>collinearList (a#xs) \<Longrightarrow> \<not>collinearList (xs)"
  apply (simp add: collinearList_def, safe)
  apply (erule_tac x="aa+1" in allE, simp, erule_tac x="b+1" in allE, simp)
by (erule_tac x="c+1" in allE, simp)
(*collinearList reverse is still a collinearList*)
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

(*extend collinearList is still a collinearList*)
lemma collinearListAppend1 [simp]: "collinearList xs \<Longrightarrow> collinearList (a#xs)"
  by (metis collinearList2)
lemma collinearListAppendB [simp]: "collinearList xs \<Longrightarrow> collinearList (x @ xs)"
  by (induction x, simp+)
lemma collinearListAppend2 [simp]: "collinearList xs \<Longrightarrow> collinearList (xs @ [a])"
  by (metis collinearList2 collinearListRev rev.simps(2) rev_rev_ident)
lemma collinearListAppend [simp]: "collinearList xs \<Longrightarrow> collinearList (xs @ x)"
  apply (cases xs, simp)
  apply (simp add: collinearList_def, safe)+
  apply (rule_tac x="aa" in exI, simp, rule_tac x=b in exI, simp, rule_tac x=c in exI, simp)
by (metis append_Cons length_Cons nth_append)


(*no 3 corners behind each other are collinear if \<not>collinearList L*)
lemma collinearListAdj: "\<not>collinearList L \<Longrightarrow> a < length L - 2 \<Longrightarrow>
    \<not>collinear (L ! a)(L! Suc a)(L! Suc(Suc a))"
  apply (simp add: collinearList_def, erule_tac x=a in allE, safe)
  apply (metis diff_less_Suc lessI less_trans_Suc lift_Suc_mono_less_iff)
  apply (erule_tac x="Suc a" in allE, safe, metis Suc_lessD add_2_eq_Suc' less_diff_conv)
by (erule_tac x="Suc (Suc a)" in allE, safe, (simp add: less_diff_conv n_not_Suc_n)+)



(*none of the segments from point list intersects(real) with another segment form this point list*)
definition crossingFreePList :: "point2d list \<Rightarrow> bool" where
 "crossingFreePList P \<equiv> \<forall>i k. ((k < length P - 1 \<and> i < length P - 1) \<longrightarrow>
 \<not>crossing (P ! i) (P ! Suc i) (P ! k) (P ! Suc k))"

(*none of the segments from the point list intersect with another segment of the point list
  (except of course the each adjacent edge)*)
definition intersectionFreePList :: "point2d list \<Rightarrow> bool" where
 "intersectionFreePList P \<equiv> (\<forall>i k. ((k < length P - 1 \<and> i < length P - 1
  \<and> (P!i) \<noteq> (P!k) \<and> (P ! i) \<noteq> (P ! Suc k) \<and> (P ! Suc i) \<noteq> (P ! k)) \<longrightarrow>
    \<not>intersect (P ! i) (P ! Suc i) (P ! k) (P ! Suc k))
  \<and> \<not>collinear (P!0)(P!1)(P!2))"
lemma intersectionFreePListAdjacentColl: "pointList P \<Longrightarrow> intersectionFreePList P \<Longrightarrow>
  \<forall> i < length P - 2. \<not>pointOnSegment (P!i) (P!Suc i) (P!Suc(Suc i))"
  apply (auto simp add: intersectionFreePList_def pointOnSegment_def)
  apply (subgoal_tac "segment (P ! Suc i) (P ! Suc (Suc i))")
  apply (auto simp add: pointOnSegment_def)
oops

(*if in the first place no intersection, then at the second position*)
lemma sizeOfList: "\<not> intersect a b A B \<Longrightarrow> intersect ((a#b# L) ! k) ((a#b# L) ! Suc k) A B \<Longrightarrow> k\<ge>1"
  by (cases k, auto)
lemma listIntersectNth: "\<not>intersect a b A B \<Longrightarrow> intersect ((a#b# L) ! i) ((a#b# L) ! Suc i) A B \<Longrightarrow>
  intersect ((b#L) ! (i - 1)) ((b#L) ! (Suc i - 1)) A B"
  by (cut_tac A=A and B=B and a=a and b=b and L=L and k=i in sizeOfList, auto)

(*if a segment from the segment list and the segment AB intersects, then the extension of this list,
 intersect with the segment AB too*)
lemma listIntersectionAppend: "segment A B \<Longrightarrow> i < length L - 1 \<Longrightarrow>
  intersect (L ! i) (L ! Suc i) A B \<Longrightarrow> \<exists>k l::nat. 0 \<le> k \<and> l = k + 1 \<and> l < length (a # b # L)
  \<and> intersect ((a # b # L) ! k) ((a # b # L) ! l) A B"
  by (rule_tac x="i + 2" in exI, rule_tac x="i + 3" in exI, auto)
lemma listIntersectionDel : "segment A B \<Longrightarrow> length L \<ge> 1 \<Longrightarrow> \<not>intersect a b A B \<Longrightarrow>
  (\<exists> k. k \<ge> 0 \<and> (k + 1) < length (a # b # L) \<and> intersect ((a#b# L) ! k) ((a#b# L) ! (k + 1)) A B)
  \<longleftrightarrow> ((\<exists> i. i\<ge>0 \<and> i + 1 < length L \<and> intersect (L!i) ( L!(i + 1)) A B) \<or> intersect b (hd L) A B)"
  apply (auto, rule_tac x="k - 2" in exI, subgoal_tac "k \<ge> 2")
  apply (auto, subgoal_tac "Suc (k - 2) = k - 1 \<and> (k - 2) = k - Suc (Suc 0)", auto)
  apply (metis One_nat_def Suc_1 hd_conv_nth le_0_eq le_Suc_eq length_0_conv not_less_eq_eq
    nth_Cons_0 nth_Cons_Suc)
  apply (rule_tac x="1" in exI, auto, subgoal_tac "L ! 0 = hd L")
by (auto, metis Suc_n_not_le_n gen_length_code(1) hd_conv_nth length_code)
lemma listIntersection1: "segment A B \<Longrightarrow> length L \<ge> 1 \<Longrightarrow> \<not> intersect a b A B \<Longrightarrow>
  (intersect ((a#b#L)!k) ((a#b#L)!Suc k) A B
  \<longleftrightarrow> ( k\<ge>2 \<and> intersect (L ! (k - 2)) ( L ! (k - 1)) A B)) \<or> intersect b (hd L) A B"
  apply (safe,metis (erased, hide_lams) Suc_eq_plus1 add.commute add_leE hd_conv_nth not_less_eq_eq
    list.size(3) monoid_add_class.add.right_neutral  nth_Cons_0 nth_Cons_Suc one_add_one le_antisym)
  apply (subgoal_tac "k \<ge> 2", subgoal_tac "(k - Suc (Suc 0)) = k - 2")
  apply (simp, simp, simp)
  apply (metis One_nat_def Suc_1 hd_conv_nth le_0_eq le_Suc_eq length_0_conv not_less_eq_eq
    nth_Cons_0 nth_Cons_Suc)
by (subgoal_tac "(k - Suc (Suc 0)) = k - 2", auto)

theorem listIntersection: "segment A B \<Longrightarrow> length L \<ge> 1 \<Longrightarrow>
  (intersect ((a#b#L) ! k) ((a#b# L) ! Suc k) A B) \<longleftrightarrow> ((k = 0 \<and> intersect a b A B)
    \<or> (k = 1 \<and> intersect b (hd L) A B)) \<or> (k\<ge>2 \<and> intersect ( L ! (k - 2)) ( L ! (k - 1)) A B)"
  apply (safe, simp, simp, metis less_2_cases not_less nth_Cons_0, simp)
  apply (metis One_nat_def diff_self_eq_0 hd_conv_nth le_imp_less_Suc length_0_conv less_2_cases
    less_imp_le_nat not_less nth_Cons')
  apply (metis One_nat_def listIntersection1 nth_Cons_Suc)
  apply (simp , metis Suc_1 diff_0_eq_0 diff_Suc_eq_diff_pred diff_self_eq_0
    diffs0_imp_equal nth_Cons' old.nat.exhaust)
  apply (simp, metis One_nat_def Suc_1 Suc_pred diff_Suc_eq_diff_pred neq0_conv nth_Cons')
  apply (metis Suc_1 diff_Suc_1 diff_Suc_eq_diff_pred intersectNext nth_Cons' nth_Cons_Suc)
  apply (metis  listIntersection1, simp, simp)
by (metis One_nat_def hd_conv_nth list.size(3) not_one_le_zero, simp, metis One_nat_def Suc_1)





(*alte Definition*)

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
