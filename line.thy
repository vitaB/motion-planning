theory line
imports point
begin

(*definition pt1 :: point2d where "pt1 \<equiv> (| xCoord = 1, yCoord = 4 |)"
definition pt2 :: point2d where "pt2 \<equiv> (| xCoord = 2, yCoord = 6 |)"
(*Falsch. alle Punkte die ungleich sind, sind damit Strecken.
Es sollen aber nur ausgewählte Strecken angeschaut werden.*)
definition line1 :: "point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"line1 a b = (\<not> pointsEqual a b)"
lemma "line1 p r \<longleftrightarrow> p \<noteq> r" by (auto simp add: line1_def pointsEqual)
(*Zugreifen auf die Punkte?*)
typedef segment1 =  "{(A::point2d,B::point2d). A \<noteq> B}"
  apply (auto) apply (rule_tac x = pt1 in  exI) apply (rule_tac x = pt2 in  exI)
  apply (simp add: pt1_def pt2_def)
done
thm Rep_segment1
thm Abs_segment1_cases
definition segm1 :: segment1 where "segm1 \<equiv> Abs_segment1 (pt1, pt1)"*)

record line =
  sPoint :: point2d
  ePoint :: point2d
definition l1 :: line where "l1 \<equiv> \<lparr>sPoint = \<lparr> xCoord = 1, yCoord = 4 \<rparr>, ePoint = (| xCoord = 3, yCoord = 1 |)\<rparr>"
definition l2 :: line where "l2 \<equiv> \<lparr>sPoint = \<lparr> xCoord = 1, yCoord = 1 \<rparr>, ePoint = (| xCoord = 4, yCoord = 4 |)\<rparr>"
definition segment :: "line \<Rightarrow> bool" where "segment A  \<equiv> (sPoint A \<noteq> ePoint A)"

(*update segment*)

(*segmentEqual*)
lemma segment_Same : "segment A \<Longrightarrow> segment B \<Longrightarrow> A = B \<longleftrightarrow> sPoint A = sPoint B \<and> ePoint A = ePoint B"
  apply (rule iffI)
  apply (simp)
  apply (erule conjE)
  apply (simp)
done
definition segmentEqual :: "line \<Rightarrow> line \<Rightarrow> bool" where
"segment A \<Longrightarrow> segment B \<Longrightarrow> segmentEqual A B \<equiv> (A = B \<or> sPoint A = ePoint B \<and> ePoint A = sPoint B)"
  
(*Punkt links von line. berechnung durch Kreuzprodukt. kreuz < 0 im Uhrzeigersinn (punkt liegt rechts von der Strecke)
kreuz = 0 punkte liegen alle auf der selben Linie. kreuz > 0 gegen den Uhrzeigersinn *)
definition kreuz :: "line \<Rightarrow> point2d \<Rightarrow> real" where
  "kreuz A p \<equiv> signedArea (sPoint A) (ePoint A) p"
(*kreuzprodukt = 0 wenn 3 punkte kollinear*)
lemma kreuz_collinear : "kreuz A p = 0 \<longleftrightarrow> collinear (sPoint A) (ePoint A) p"
  apply (simp add: kreuz_def colliniearRight)
  apply (simp add: signedArea_def)
  apply (algebra)
done

(*Punkt auf der line*)
definition point_on_segment :: "line \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A \<Longrightarrow> (point_on_segment A p \<equiv> min (getX (sPoint A))(getX (ePoint A)) \<le> getX p
\<and> getX p \<le> max (getX (sPoint A))(getX (ePoint A)) \<and> min (getY (sPoint A))(getY (ePoint A)) \<le> getY p
\<and> getY p \<le> max (getY (sPoint A))(getY (ePoint A)))"
(* zwischenPunkt p von segment A liegt A*)
lemma segment_betwpoint : " segment A \<Longrightarrow> betwpoint p (sPoint A) (ePoint A) \<longrightarrow> point_on_segment A p"
  apply (rule impI)
  apply (simp add: betwpoint_def point_on_segment_def)
  apply (erule_tac x = 2 in allE)
  apply (simp)
  apply (auto)
done

(*intersection (line a, line b) echtes Schneiden, unechtes Schneiden*)
definition echtesSchneiden :: "line \<Rightarrow> line \<Rightarrow> bool" where
"segment A \<Longrightarrow> segment B \<Longrightarrow> echtesSchneiden A B \<equiv>
  let a = signedArea (sPoint B) (ePoint B) (sPoint A) in 
  let b = signedArea (sPoint B) (ePoint B) (ePoint A) in
  let c = signedArea (sPoint A) (ePoint A) (sPoint B) in
  let d = signedArea (sPoint A) (ePoint A) (ePoint B) in
    ((a > 0 \<and> b < 0) \<or> (a < 0 \<and> b > 0)) \<and> ((c > 0 \<and> d < 0) \<or> (c < 0 \<and> d > 0))"
lemma "segment l1 \<Longrightarrow> segment l2 \<Longrightarrow> echtesSchneiden l1 l2"
  apply (auto simp add: echtesSchneiden_def)
  apply (auto simp add: l1_def l2_def signedArea_def)
done
definition intersect :: "line \<Rightarrow> line \<Rightarrow> bool" where
"segment A \<Longrightarrow> segment B \<Longrightarrow> intersect A B \<equiv>
  let a = signedArea (sPoint B) (ePoint B) (sPoint A) in 
  let b = signedArea (sPoint B) (ePoint B) (ePoint A) in
  let c = signedArea (sPoint A) (ePoint A) (sPoint B) in
  let d = signedArea (sPoint A) (ePoint A) (ePoint B) in
   ((a > 0 \<and> b < 0) \<or> (a < 0 \<and> b > 0)) \<and> ((c > 0 \<and> d < 0) \<or> (c < 0 \<and> d > 0))
   \<or> (a = 0 \<or> point_on_segment B (sPoint A))
   \<or> (b = 0 \<or> point_on_segment B (ePoint A))
   \<or> (c = 0 \<or> point_on_segment A (sPoint B))
   \<or> (d = 0 \<or> point_on_segment A (ePoint B))"

end
