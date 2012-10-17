type vertex.
type graph.

cnst empt : vertex.
cnst dummy_vertex : vertex.

op in_graph : (graph, vertex) -> bool.

op in_graph_edge : (graph, vertex, vertex) -> bool.

op is_empty : graph -> bool.

op size : graph -> int.

op weight : graph -> int.

op degree : (graph, vertex) -> int.

op remove_vertex : (graph, vertex) -> graph.

axiom not_is_empty : forall (g:graph,v:vertex),
  in_graph(g,v) => !is_empty(g).

axiom is_empty_size : forall (g:graph), is_empty(g) => size(g)=0.

axiom size_1_inversion : forall (g:graph), size(g)=1 =>
    forall (x:vertex,y:vertex), in_graph(g,x) && in_graph(g,y) => x=y.


axiom degree_le_weight : forall (g:graph,x:vertex), 2*degree(g,x) <= weight(g).
 
axiom size_eq : forall (g1:graph,g2:graph), forall (x:vertex),
  in_graph(g1,x)=in_graph(g2,x) => size(g1)=size(g2).


axiom remove_vertex_size : forall (g:graph,v:vertex),
  in_graph(g,v) => size(remove_vertex(g,v))+1=size(g).

axiom remove_vertex_eq : forall (g:graph,v:vertex),
  in_graph(remove_vertex(g,v),v)=false.

axiom remove_vertex_neq : forall (g:graph,x:vertex,v:vertex),
x<>v => in_graph(g,v)=in_graph(remove_vertex(g,x),v).

axiom in_graph_remove_vertex : forall (g:graph,g':graph),
  (forall (x:vertex), in_graph(g,x)=in_graph(g',x) =>
  forall (v:vertex,z:vertex), in_graph(remove_vertex(g,v),z) = in_graph(remove_vertex(g',v),z)
).


axiom extensionality : forall (g1:graph,g2:graph),
  (forall (x:vertex), in_graph(g1,x)=in_graph(g2,x))
  &&
  (forall (x:vertex,y:vertex), in_graph_edge(g1,x,y)=in_graph_edge(g2,x,y) )
  =>
  g1=g2.


axiom in_graph_edge_sym : forall (g:graph,v:vertex,v':vertex),
  in_graph_edge(g,v,v') =in_graph_edge(g,v',v).


axiom edge_vertex : forall (g:graph,v:vertex,v':vertex),
  in_graph_edge(g,v,v') => in_graph(g,v) && in_graph(g,v').

axiom in_graph_remove_edge_neq: forall (g:graph,v:vertex,v':vertex,x:vertex),
  in_graph_edge(g,v,v')  && x<>v && x<>v'
  => in_graph_edge(remove_vertex(g,x),v,v').


axiom in_graph_remove_edge_conv : forall (g:graph, v:vertex, v':vertex, x:vertex),
 in_graph_edge(remove_vertex(g,x),v,v') =>
 in_graph_edge(g,v,v').


axiom weight_diff : forall (g1:graph,g2:graph,t:vertex,u:vertex),
  (forall (x:vertex), in_graph(g1,x)=in_graph(g2,x)) &&
  in_graph_edge(g2,t,u) 
    &&
  (forall (x:vertex,y:vertex), in_graph_edge(g2,x,y)
    => (in_graph_edge(g1,x,y) || (x=t && y=u) || (x=u && y=t) ))
      &&
  (forall (x:vertex,y:vertex), in_graph_edge(g1,x,y) => (in_graph_edge(g2,x,y)))
  => weight(g1)+2=weight(g2).


axiom degree_diff_neq : forall (g1:graph,g2:graph,t:vertex,u:vertex),
  (forall (x:vertex), in_graph(g1,x)=in_graph(g2,x)) &&
  in_graph_edge(g2,t,u) &&
  ( forall (x:vertex,y:vertex), in_graph_edge(g2,x,y) =>
    (in_graph_edge(g1,x,y) || (x=t && y=u) || (x=u && y=t)))
  &&
  (forall (x:vertex,y:vertex), in_graph_edge(g1,x,y) && in_graph_edge(g2,x,y)) => 
  (forall (a:vertex), a <> t && a <> u => degree(g1,a)=degree(g2,a)).
  


axiom degree_diff_eq : forall (G1:graph, G2:graph, t:vertex, u:vertex),
  (forall (x:vertex), in_graph(G1,x) = in_graph(G2,x)) &&
  in_graph_edge(G2,t,u) &&
  (forall (x:vertex,y:vertex), in_graph_edge(G2,x,y) => 
   (in_graph_edge(G1,x,y)= true || (x=t && y=u) || (x=u && y = t))) &&  
  (forall (x:vertex,y:vertex), in_graph_edge(G1,x,y) => in_graph_edge(G2,x,y)) => 
  degree(G2,t) = degree(G1,t)+1 && degree(G2,u) = degree(G1,u)+1.


axiom remove_vertex_diff_1 : forall (G1:graph,G2:graph,u:vertex,v:vertex),
  (forall (x:vertex), in_graph(G1,x)= in_graph(G2,x)) &&
  (forall (x:vertex,y:vertex),in_graph_edge(G1,x,y) => in_graph_edge(G2,x,y)) &&
  in_graph_edge(G2,u,v) &&
  (forall (x:vertex,y:vertex),
    in_graph_edge(G2,x,y) =>
      (in_graph_edge(G1,x,y) || (x = u && y = v) || (x = v && y = u))) =>
  remove_vertex(G1,u) = remove_vertex(G2,u).




pred diff1(G1:graph,G2:graph,t:vertex,u:vertex) = 
  (forall (x:vertex), in_graph(G1,x)= in_graph(G2,x)) &&
  (* /* in_graph_edge(G2,t,u) && */ *)
  (forall (x:vertex,y:vertex), in_graph_edge(G2,x,y) => 
   (in_graph_edge(G1,x,y)= true || (x=t && y=u) || (x = u && y = t))) &&  
  (forall (x:vertex,y:vertex), in_graph_edge(G1,x,y) => in_graph_edge(G2,x,y))
.


cnst eps:real.
axiom eps_def : 0%r<eps. 
cnst t : vertex.
cnst u : vertex.


pop choose : (graph,real,int,int) -> vertex.

spec choose_tu(g1:graph,g2:graph,n:int,i1:int,i2:int,eps:real) : 
  v1=choose(g1,eps,n,i1); assert (t=v1 || u=v1) ~ 
  v2=choose(g2,eps,n,i2); assert (t=v2 || u=v2) :
i1=i2 ==[exp(eps/4%r);0%r]==> v1=v2.


spec choose_ntu(g1:graph,g2:graph,n:int,i1:int,i2:int,eps:real) : 
  v1=choose(g1,eps,n,i1); assert (t<>v1 && u<>v1) ~ 
  v2=choose(g2,eps,n,i2); assert (t<>v2 && u<>v2) :
i2=i2 ==[exp(2%r/((n%r-i1%r)*((4%r/eps)*((1%r)^(1%r/2%r)))));0%r]==> v1=v2.




cnst n : int.

game G = {
  fun vertex_cover(g:graph): vertex list = { 
    var pi : vertex list = [];
    var i : int = 0;
    var v : vertex;
    while (i<n) {
      v = choose(g,eps,n,i);
      pi = v :: pi;
      g = remove_vertex(g,v);
      i = i + 1;
    }
    return pi;
  }
}
.


axiom real_le_sym : forall (x:real), x <= x.
axiom real_comm : forall (x:real,y:real), x*y=y*x.
axiom real_one : forall (x:real), x*1%r = x.
axiom real_zero : forall (x:real), x*0%r=0%r.
axiom pow_zero : forall (x:real), (x)^(0%r)=1%r.
axiom pow_one : forall (x:real), (1%r)^x=1%r.
axiom pow_exp : forall (x:real,y:real), exp(x)^y = exp(x*y).
axiom real_exp_zero : 1%r<=exp(0%r).
axiom real_exp_pos : forall (x:real), 0%r<x => 1%r<exp(x).
axiom real_exp_mon : forall (x:real,y:real), x<y => exp(x)<exp(y).
axiom real_mul_pos : forall (x:real,y:real), 0%r<=x && 0%r<=y => 0%r <= x*y.
axiom div_le : forall (x:real,y:real), x<=y => 1%r<=y/x.





(* the annoying size(g)=cte is to avoid a technical problem *)
equiv vertex_coverDP : G.vertex_cover ~ G.vertex_cover : 
  ( diff1(g{1},g{2},t,u) && size(g{1})=2 && n=size(g{1}) ) ==[exp((5%r/4%r)*eps);0%r]==> ={res}.
while i->exp(2%r/((n%r-i%r)*((4%r/eps)*((1%r)^(1%r/2%r))))), exp(eps/4%r),i{1},0,2 : 
         diff1(g{1},g{2},t,u) 
         && 2=n
         && ={i,pi}
         && 0<=i{1} && i{1}<=n
         && ((mem(t,pi{1})  || mem(u,pi{1}))  => ={g})
         && ((mem(t,pi{1})=false && mem(u,pi{1})=false) => diff1(g{1},g{2},t,u))
    : mem(t,pi)|| mem(u,pi),mem(t,pi)||mem(u,pi).
(* first premise: init *)
auto. (* we are not proving the approximation yet *)
(* snd (fifth) premise: termination and stabilization of p1 *) 
wp; rnd; trivial.
(* third premise : neg p1, neg p1*)
swap -3.
wp 2 2.
apply : choose_ntu(g{1},g{2},n,i{1},i{2},eps); trivial.
(* forth premise: neg p1, p1 *)
swap -3.
wp 2 2.
apply : choose_tu(g{1},g{2},n,i{1},i{2},eps); trivial.
save.



