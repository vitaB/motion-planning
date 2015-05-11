theory line
imports point
begin

definition segment :: "point2d \<Rightarrow> point2d  \<Rightarrow> bool" where
"segment a b \<equiv> \<not> pointsEqual a b"

definition point_on_segment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> point_on_segment p A B \<equiv>  min (getX A)(getX B) \<le> getX p \<and>
getX p \<le> max (getX A)(getX B) \<and> min (getY A)(getY B) \<le> getY p
\<and> getY p \<le> max (getY A)(getY B)"

(* zwischenPunkt p von segment A B liegt auf A B*)
lemma segment_betwpoint : " segment A B \<Longrightarrow> betwpoint p A B \<longrightarrow> point_on_segment p A B"
  apply (rule impI)
  apply (simp add: betwpoint_def point_on_segment_def)
  apply (erule_tac x = 2 in allE)
  apply (simp)
  apply (auto)
done

(*Schnittpunkt zwischen Segment A B und Segment P R*)
definition intersect :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> segment P R \<Longrightarrow> intersect A B P R \<equiv>
  let a = signedArea P R A in
  let b = signedArea P R B in
  let c = signedArea A B P in
  let d = signedArea A B R in
   ((a > 0 \<and> b < 0) \<or> (a < 0 \<and> b > 0)) \<and> ((c > 0 \<and> d < 0) \<or> (c < 0 \<and> d > 0))
   \<or> (a = 0 \<or> point_on_segment A P R)
   \<or> (b = 0 \<or> point_on_segment B P R)
   \<or> (c = 0 \<or> point_on_segment P A B)
   \<or> (d = 0 \<or> point_on_segment R A B)"






(* Line soll kein eigener Datentyp mehr sein!
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
lemma "segment l1 \<Longrightarrow> segment \<lparr>sPoint = \<lparr> xCoord = 1, yCoord = 1 \<rparr>, ePoint = (| xCoord = 3, yCoord = 1 |)\<rparr>
\<Longrightarrow> intersect l1 \<lparr>sPoint = \<lparr> xCoord = 1, yCoord = 1 \<rparr>, ePoint = (| xCoord = 3, yCoord = 1 |)\<rparr>"
  apply (auto simp add: intersect_def)
  apply (auto simp add: l1_def l2_def signedArea_def)
done


lemma "segment l1 \<Longrightarrow> segment l2 \<Longrightarrow> echtesSchneiden l1 l2"
  apply (auto simp add: echtesSchneiden_def)
  apply (auto simp add: l1_def l2_def signedArea_def)
done
definition r1 :: line where "r1 \<equiv> \<lparr>sPoint = \<lparr> xCoord = 2, yCoord = 1 \<rparr>, ePoint = (| xCoord = 2, yCoord = 2 |)\<rparr>"
definition r2 :: line where "r2 \<equiv> \<lparr>sPoint = \<lparr> xCoord = 1, yCoord = 3 \<rparr>, ePoint = (| xCoord = 3, yCoord = 3 |)\<rparr>"
lemma "segment r1 \<Longrightarrow> segment r2 \<Longrightarrow> \<not> intersect r1 r2"
  apply (auto simp add: intersect_def)
  apply (auto simp add: r1_def r2_def signedArea_def simp add: point_on_segment_def)
done
*)
end
