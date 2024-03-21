ghost function U<T> (S : set<set>) : set
{
  if S == {} then {}
  else var s := pick (S) ;
       U (S - {s}) + s
}
ghost function pick<T> (s : set) : T
  requires s != {}
{var x :| x in s ; x}

lemma strict_incl_size<T> (s1 : set, s2 : set)
  requires s1 < s2
  ensures |s1| < |s2|
{
  if s1 == {} {}
  else {
    var a :| a in s1 ;
    strict_incl_size (s1 - {a}, s2 - {a}) ;
  }
}

lemma incl_size<T> (s1 : set, s2 : set)
  requires s1 <= s2
  ensures |s1| <= |s2|
{
  if s1 < s2 {strict_incl_size (s1, s2) ;}
  else {assert s1 == s2 ;}
}

lemma incl_eq_size<T> (s1 : set, s2 : set)
  requires s1 <= s2 && |s1| == |s2|
  ensures s1 == s2
{
  if s1 == s2 {}
  else {
    strict_incl_size (s1, s2) ;
  }
}

type Vertex = nat
type Vertices = set<Vertex>

type Edge = set<Vertex>
type Edges = set<Edge>

predicate edge_size2 (e : Edge)
{
  |e| == 2
}

predicate edge_over (vs : Vertices, e : Edge)
{
  edge_size2 (e) && e <= vs
}

type Graph = (Vertices, Edges)

predicate ok_g (g : Graph)
{
  forall e :: e in g.1 ==> edge_over (g.0, e)
}

lemma at_lst_one_edge_at_lst_two_vertices (g : Graph)
  requires ok_g (g)
  ensures (exists e :: e in g.1) ==> |g.0| > 1
{
  calc{ exists e :: e in g.1 ;
  ==> {var e :| e in g.1 ; assert |e| == 2 && e <= g.0 ; incl_size (e, g.0) ;}
    |g.0| > 1 ;
  }
}

ghost function Union (gs : set<Graph>) : Graph
  requires forall g :: g in gs ==> ok_g (g)
{
  (U (set g <- gs :: g.0),
   U (set g <- gs :: g.1))
}

predicate sub_graph (g1  : Graph, g2 : Graph)
  requires ok_g (g1) && ok_g(g2)
{
  g1.0 <= g2.0 && g1.1 <= g2.1
}

predicate disjoint (g1  : Graph, g2 : Graph)
  requires ok_g (g1) && ok_g(g2)
{
  g1.0 !! g2.0
}

ghost predicate thru (g1  : Graph, g2 : Graph, e : Edge)
  requires edge_size2 (e)
  requires ok_g (g1) && ok_g(g2)
  requires disjoint (g1, g2)
{
  var v0 :| v0 in e ; assert |e - {v0}| == 1 ;
  var v1 :| v1 in (e - {v0}) ;
  (v0 in g1.0 && v1 in g2.0) || (v1 in g1.0 && v0 in g2.0)
}

ghost predicate tree (g : Graph)
  requires ok_g (g)
  decreases |g.0|
{
  |g.0| == 1
  ||
  exists t : Graph, t' : Graph, e : Edge :: ok_g (t) && ok_g (t') && edge_size2 (e)
                                            && disjoint (t, t')
                                            && thru (t, t', e)
                                            && g.0 == t.0 + t'.0
                                            && g.1 == t.1 + t'.1 + {e}
                                            && tree(t) && tree (t')
}

lemma tree_number_of_edges_n_vertices (g : Graph)
  requires ok_g (g)
  requires tree (g)
  ensures |g.0| == |g.1| + 1
  decreases |g.0|
{
  if |g.0| == 1 {
    at_lst_one_edge_at_lst_two_vertices (g) ;
  }
  else {
    var t : Graph, t' : Graph, e : Edge :| ok_g (t) && tree (t) && ok_g (t') && tree (t') && edge_size2(e)
                                           && disjoint (t, t') && thru (t, t', e) && g.0 == t.0 + t'.0 && g.1 == t.1 + t'.1 + {e} ;
    calc{
      |g.0| ;
    ==
      |t.0| + |t'.0| ;
    == {tree_number_of_edges_n_vertices (t) ; tree_number_of_edges_n_vertices (t') ;}
      (|t.1| + 1) + (|t'.1| + 1) ;
    == {assert |g.1| == |t.1| + |t'.1| + 1 ;}
      |g.1| + 1 ;
    }
  }
}

predicate covers (g : Graph, g' : Graph)
  requires ok_g (g) && ok_g (g')
{
  g.0 == g'.0 && g.1 <= g'.1
}


ghost predicate covering_tree (g : Graph, t : Graph)
  requires ok_g (t) && ok_g (g)
{
  tree (t) && covers (t, g)
}


ghost predicate connected (g : Graph)
  requires ok_g (g)
{
  exists t : Graph :: ok_g (t) && covering_tree (g, t)
}

ghost predicate forest (g : Graph)
  requires ok_g (g)
{
  exists ts : set<Graph> ::
    (forall t : Graph :: t in ts ==> ok_g (t) && sub_graph (t, g))
    &&
    (forall t : Graph :: t in ts ==> tree (t))
    &&
    (forall t1, t2 :: t1 in ts && t2 in ts && t1 != t2 ==> disjoint (t1, t2))
    &&
    g == Union (ts)
}

ghost predicate safe (g : Graph, e : Edge)
  requires edge_size2 (e)
  requires ok_g(g) && forest (g)
{
  var ts : set<Graph> :|
    (forall t : Graph :: t in ts ==> ok_g (t) && sub_graph (t, g) && tree (t))
    &&
    (forall t1, t2 :: t1 in ts && t2 in ts && t1 != t2 ==> disjoint (t1, t2))
    &&
    g == Union (ts) ;
  exists t1, t2 :: t1 in ts && t2 in ts && t1 != t2 && assert disjoint (t1, t2); thru (t1, t2, e)
}

type Weighted_Graph = (Graph, map<Edge, nat>)

predicate ok_wg (w : Weighted_Graph)
{
  ok_g (w.0) &&
  w.1.Keys == w.0.1
}

ghost function cost (w : Weighted_Graph, g : Graph) : nat
  requires ok_g (g) && ok_wg (w)
  requires g.1 <= w.0.1
{
  sum_values (w.1, g.1)
}
ghost function sum_values<T> (vs : map<T, nat>, ks : set) : nat
  requires vs.Keys >= ks
{
  if ks == {} then 0
  else var k :| k in ks ;
       vs [k] + sum_values (vs, ks - {k})
}

ghost predicate mct (w : Weighted_Graph, t : Graph)
  requires ok_wg (w)
{
  ok_g (t)
  &&
  covering_tree (w.0, t)
  &&
  forall t' :: ok_g (t') && covering_tree (w.0, t') ==> cost (w, t) <= cost (w, t')
}

method kruskal (w : Weighted_Graph) returns (opt : Graph)
  requires ok_wg (w)
  requires connected (w.0)
  ensures mct (w, opt)
{
  opt := (w.0.0, {}) ;
  init_wf (w) ; init (w) ;
  while |opt.1| != |opt.0| - 1
    invariant ok_g (opt) && forest (opt)
    invariant exists t :: mct (w, t) && covers (opt, t)
    invariant |opt.1| < |opt.0|
    decreases |opt.0| - |opt.1|
  {
    var e := lightest_safe (w, opt) ;
    safe_fresh (opt, e) ;
    opt := (opt.0, opt.1 + {e}) ;
    assume ok_g (opt) && forest (opt) ;
    assume exists t :: mct (w, t) && covers (opt, t) ;
  }
  end_chk (w, opt) ;
}

lemma init_wf (w : Weighted_Graph)
  requires ok_g (w.0)
  ensures ok_g ((w.0.0, {})) && forest((w.0.0, {}))
{
  var ts : set<Graph> := set v <- w.0.0 :: ({v}, {}) ;
  assert ok_g ((w.0.0, {})) ;
  assert (forall t : Graph :: t in ts ==> ok_g (t) && sub_graph (t, (w.0.0, {}))) ;
  assert (forall t : Graph :: t in ts ==> ok_g (t) && tree (t)) ;
  assert (forall t1, t2 :: t1 in ts && t2 in ts && t1 != t2 ==> disjoint (t1, t2)) ;
  assume (w.0.0, {}) == Union (ts) ;
  assert (exists ts : set<Graph> ::
            (forall t : Graph :: t in ts ==> ok_g (t) && tree (t))
            &&
            (forall t1, t2 :: t1 in ts && t2 in ts && t1 != t2 ==> disjoint (t1, t2))
            &&
            (w.0.0, {}) == Union (ts)) by {
    assert ok_g ((w.0.0, {})) &&
           (forall t : Graph :: t in ts ==> ok_g (t) && sub_graph (t, (w.0.0, {}))) &&
           (forall t : Graph :: t in ts ==> ok_g (t) && tree (t)) &&
           (forall t1, t2 :: t1 in ts && t2 in ts && t1 != t2 ==> disjoint (t1, t2)) &&
           (w.0.0, {}) == Union (ts) ;
  }
}

lemma init (w : Weighted_Graph)
  requires ok_wg (w)
  requires connected (w.0)
  ensures exists t :: mct (w, t) && covers ((w.0.0, {}), t)

lemma end_chk (w : Weighted_Graph, f : Graph)
  requires ok_wg (w) && ok_g (f)
  requires exists t :: mct (w, t) && covers (f, t)
  requires |f.1| == |f.0| - 1
  ensures mct (w, f)
{
  ghost var t :| mct (w, t) && covers (f, t) ;
  calc{
    covers (f, t) ;
  ==>
    f.0 == t.0 && f.1 <= t.1 ;
  ==> {assert |f.1| == |f.0| - 1 == |t.0| - 1 ;}
    |f.1| == |t.0| - 1 ;
  ==> {tree_number_of_edges_n_vertices (t) ;}
    |t.1| == |f.1| == |t.0| - 1 ;
  ==> {assert f.1 <= t.1 ; incl_eq_size (f.1, t.1) ;}
    f.1 == t.1 ;
  ==> {}
    f == t ;
  ==> {assert mct (w, t) ;}
    mct (w, f) ;
  }
}

method lightest_safe (w : Weighted_Graph, f : Graph) returns (e : Edge)
  requires ok_wg (w)
  requires connected (w.0)
  requires ok_g (f) && forest (f)
  requires exists t :: mct (w,t) && covers (f, t)
  requires |f.1| < |f.0| - 1
  ensures e in w.0.1
  ensures safe (f, e) && forall e' :: e' in w.0.1 && safe (f, e') ==> w.1[e] <= w.1[e']

lemma safe_fresh (f : Graph, e : Edge)
  requires ok_g (f) && forest (f)
  requires edge_size2 (e)
  requires safe (f, e)
  ensures e !in f.1
