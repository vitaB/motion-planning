theory line
imports point
begin

(*Definition für Segment.*)
(*Evtl. wäre ein eigener Datentyp besser*)
definition segment :: "point2d \<Rightarrow> point2d  \<Rightarrow> bool" where
"segment a b \<equiv> \<not> pointsEqual a b"

definition segment_Same :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> segment P R \<Longrightarrow> segment_Same A B P R \<equiv> (pointsEqual A P \<and> pointsEqual B R)"

definition point_on_segment :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> point_on_segment p A B \<equiv>  min (xCoord A)(xCoord B) \<le> xCoord p \<and>
xCoord p \<le> max (xCoord A)(xCoord B) \<and> min (yCoord A)(yCoord B) \<le> yCoord p
\<and> yCoord p \<le> max (yCoord A)(yCoord B)"

(* zwischenPunkt p von segment A B liegt auf A B*)
lemma segment_betwpoint : "segment A B \<Longrightarrow> betwpoint p A B \<longrightarrow> point_on_segment p A B"
  apply (rule impI)
  apply (simp add: betwpoint_def point_on_segment_def)
  apply (erule_tac x = 2 in allE)
  apply (simp)
  apply (auto)
done

(*(echter)Schnitt zwischen Segment A B und Segment P R*)
definition crossing ::  "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"segment A B \<Longrightarrow> segment P R \<Longrightarrow> crossing A B P R \<equiv>
  let a = signedArea P R A in
  let b = signedArea P R B in
  let c = signedArea A B P in
  let d = signedArea A B R in
   ((a > 0 \<and> b < 0) \<or> (a < 0 \<and> b > 0)) \<and> ((c > 0 \<and> d < 0) \<or> (c < 0 \<and> d > 0))"
(*Schnitt, auch wenn Endpunkt auf Strecke liegt*)
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

lemma intersectSym : "intersect A B P R \<longleftrightarrow> intersect B A P R" sorry
lemma intersectSym1 : "intersect A B P R \<longleftrightarrow> intersect P R A B" sorry

end
