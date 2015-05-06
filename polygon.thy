theory polygon
imports segmentList
begin

(*Polygon. mit mehr als 3 Ecken. und Kreislauf*)
definition polygon :: "point2d list \<Rightarrow> point2d list" where
"pointList P \<Longrightarrow> size P \<ge> 3 \<Longrightarrow> polygon P = P @ [hd P]"

(*Beweis: Kreislauf mit Punkten wo Anfangspunkt und Endpunk gleich sind. mehr als 2 Ecken
definition circuit_list :: "line list \<Rightarrow> bool" where
"connected segList \<Longrightarrow> circuit_list segList = (sPoint(hd segList) = ePoint (last segList))"*)

(* Es fehlt noch! kein segment wiederholt sich*)

(*polygon equivalent*)

(*definition polygon_eq :: "line list \<Rightarrow> line list \<Rightarrow> bool" where
"polygon_eq P R \<equiv> list_eq_iff_nth_eq P R"*)

(*intersection(Polygon, Line)*)

(*wann ist ein polygon convex*)
primrec conv_polygon :: "line list \<Rightarrow> bool" where 
  "conv_polygon [] = True"
|  " conv_polygon (x#xs) = "

definition conv_polygon :: "line list \<Rightarrow> bool" where
"polygon P \<Longrightarrow> conv_polygon P \<equiv> ()"

(*Punkt inside Polygon*)

(*intersection(Polygon, Polygon)*)
(*move Polygon*)

end
