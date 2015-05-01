theory point
imports Complex_Main
begin

(*defintion von Punkten*)
record point2d =
  xCoord :: real
  yCoord :: real
definition pt1 :: point2d where "pt1 \<equiv> (| xCoord = 1, yCoord = 4 |)"
definition pt2 :: point2d where "pt2 \<equiv> (| xCoord = 2, yCoord = 6 |)"

(*selectop von x des Punkts*)
lemma "xCoord \<lparr>xCoord = a, yCoord = b\<rparr> = a" by simp
lemma "xCoord pt1 = 1"
  apply (subst pt1_def) apply (simp)
done
(*update Points*)
lemma "pt1 \<lparr>xCoord := 0\<rparr> = (| xCoord = 0, yCoord = 4 |)"
  apply (subst pt1_def) apply (simp)
done
definition getX :: "'a point2d_scheme \<Rightarrow> real" where "getX p \<equiv> xCoord p"
definition getY :: "'a point2d_scheme \<Rightarrow> real" where "getY p \<equiv> yCoord p"
definition setX :: "'a point2d_scheme \<Rightarrow> real \<Rightarrow> 'a point2d_scheme" where
"setX p a \<equiv> p\<lparr> xCoord := a\<rparr>"
definition setY :: "'a point2d_scheme \<Rightarrow> real \<Rightarrow> 'a point2d_scheme" where
"setY p a \<equiv> p\<lparr> yCoord := a\<rparr>"
definition incX :: "'a point2d_scheme \<Rightarrow> 'a point2d_scheme" where
"incX p \<equiv> \<lparr>xCoord = xCoord p + 1, yCoord = yCoord p,\<dots> = point2d.more p\<rparr>"
lemma "incX p = setX p (getX p + 1)" by (simp add: getX_def setX_def incX_def)

(*points equal*)
lemma pointSame : "p\<lparr>xCoord := a, yCoord := b\<rparr> = p\<lparr>yCoord := b, xCoord := a \<rparr>" by simp
lemma pointSameCoord : "p = \<lparr>xCoord = xCoord p, yCoord = yCoord p\<rparr>" by simp
lemma pointSameCoord1 : "p\<lparr>xCoord := a\<rparr> = p\<lparr> xCoord := a'\<rparr> \<Longrightarrow> a = a'"
  apply (drule_tac f = xCoord in arg_cong) apply (simp)
done
lemma "p\<lparr>xCoord := a\<rparr> = p\<lparr> xCoord := a'\<rparr> \<Longrightarrow> a = a'"
  apply (rule_tac r = p in point2d.cases_scheme) (*apply (cases p)*)
  apply (simp)
done 
definition pointsEqual :: "point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"pointsEqual r p \<longleftrightarrow> (getX r = getX p \<and> getY r = getY p)"
lemma pointsEqualSame : "pointsEqual p p" by (simp add: pointsEqual_def)
lemma pointsEqual1 : "p = (| xCoord = a, yCoord = b |) \<and> r = (| xCoord = a, yCoord = b |)
  \<longrightarrow> pointsEqual p r" by (simp add: pointsEqual_def getX_def getY_def)
lemma pointsEqual2 : "pointsEqual p r \<longrightarrow> xCoord p = xCoord r \<and> yCoord p = yCoord r"
  by (simp add: pointsEqual_def getX_def getY_def)
theorem pointsEquals : "pointsEqual p r \<longleftrightarrow> p = r"
  apply (rule iffI)
    apply (simp add: pointsEqual2)
    apply (simp add: pointsEqualSame)
done

(*3 Punkte sind auf einer geraden*)
definition collinear :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"collinear a b c = ((getX a - getX b)*(getY b - getY c) = (getY a- getY b)*(getX b - getX c))"


(*Punkt a links vom Punkt b?*)
definition leftFromPoint :: "point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"leftFromPoint a b = (getX a < getX b)"
lemma "a < b \<longleftrightarrow> leftFromPoint (| xCoord = a, yCoord = c |) (| xCoord = b, yCoord = c |)"
by (auto simp add: getX_def leftFromPoint_def)

(*punkt B zwischen A und C*)
definition midpoint :: "point2d \<Rightarrow> point2d \<Rightarrow> point2d \<Rightarrow> bool" where
"midpoint a b c = (2 * getY a = getY b + getY c \<and> 2 * getX a = getX b + getX c)"

(*move/translate point*)
end
