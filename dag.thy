theory dag
imports polygon
begin

record trapez = topT :: "point2d\<times>point2d"
  bottomT :: "point2d\<times>point2d"
  leftp :: point2d
  rightp :: point2d

definition t1 :: trapez where
  "t1 \<equiv> (|topT =(Abs_point2d(1,1),Abs_point2d(1,1)), bottomT =(Abs_point2d(1,1),Abs_point2d(1,1)), leftp =Abs_point2d(1,1), rightp=Abs_point2d(1,1)|)"

record trapezoid = trapez :: trapez
  neighbor :: "trapez list"
definition tr1 :: trapezoid where
  "tr1 \<equiv> \<lparr>trapez = t1, neighbor= []\<rparr>"

datatype kNode = xNode point2d | yNode "(point2d\<times>point2d)"
definition node1 :: kNode where
  "node1 \<equiv> xNode (Abs_point2d(1,1))"
definition node2 :: kNode where
  "node2 \<equiv> yNode (Abs_point2d(1,1), Abs_point2d(1,1))"

(*directed acyclic graph*)
datatype dag = Tip trapezoid | Node " dag" kNode " dag"
value "Node (Tip tr1) node1 (Tip tr1)"
definition dag1 :: dag where
  "dag1 \<equiv> Node (Tip tr1) node1 (Node (Tip tr1) node2 (Tip tr1))"

end
