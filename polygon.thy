theory polygon
imports line
begin

(*zusammenhängende segmente*)
primrec connected :: "line list \<Rightarrow> bool" where
  "connected [] = True"
| "connected (x#xs) = (xs = [] \<or> (ePoint(x) = ePoint(hd xs) \<and> connected xs))"

(*Polygon, liste/sequenz mit Punkten wo Anfangspunkt und Endpunk gleich sind*)
definition polygon :: "line list \<Rightarrow> bool" where
"connected segList \<Longrightarrow> polygon segList \<equiv> (sPoint(hd segList) = ePoint (last segList))"
thm list_eq_iff_nth_eq
(*polygon equivalent*)
(*definition polygon_eq :: "line list \<Rightarrow> line list \<Rightarrow> bool" where
"polygon_eq P R \<equiv> list_eq_iff_nth_eq P R"*)

(*intersection(Polygon, Line)*)

(*wann ist ein polygon convex*)


(*Punkt inside Polygon*)

(*intersection(Polygon, Polygon)*)
(*move Polygon*)

end
