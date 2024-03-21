include "datatypes.dfy"

ghost predicate validGraph(g: Graph)
{
  (|nodes(g)| >= 1)
  && (forall node1: Node, node2: Node :: node1 in nodes(g) && node2 in nodes(g) ==> node1 != node2)
  && (forall edge1: Edge, edge2: Edge :: edge1 in edges(g) && edge2 in edges(g) ==> edge1 != edge2)
}

ghost predicate graphIsTree(g: Graph)
{
  validGraph(g)
  && |edges(g)| == |nodes(g)| - 1
  && forall node: Node :: node in nodes(g) ==> exists edge :: edge in edges(g)
                                                              && (source(edge) == node || target(edge) == node)
}

class Tree {
  var nodes: set<Node>
  var edges: set<Edge>

  ghost predicate Valid()
    reads this
  {
    |edges| == |nodes| - 1
    && (|edges| == 0 || (forall node: Node :: node in nodes ==>  (exists edge :: edge in edges && (node in {source(edge), target(edge)}))))
  }

  ghost predicate Covers(g: Graph)
    reads this
  {
    getNodes(g) == this.nodes && getEdges(g) <= this.edges
  }

  method GetCost() returns (cost: int)
  {
    cost := 0;
    var copyEdges := edges;
    while(copyEdges != {})
    {
      var e :| e in copyEdges;
      cost := cost + weight(e);
      copyEdges := copyEdges - { e };
    }
  }

  constructor(node: Node)
    ensures |nodes| == 1
    ensures |edges| == 0
    ensures node in nodes
    ensures Valid()
  {
    nodes := { node };
    edges := {};
  }

  constructor Clone(tree: Tree)
    requires tree.Valid()
    ensures Valid()
    ensures nodes == tree.nodes
    ensures edges == tree.edges
  {
    nodes := tree.nodes;
    edges := tree.edges;
  }

  ghost predicate IsDisjointComparedWith(t: Tree)
    reads this
    reads t
    ensures t.nodes !! this.nodes ==> (forall n :: n in this.nodes ==> n !in t.nodes) && (forall n :: n in t.nodes ==> n !in this.nodes)
    ensures t.edges !! this.edges ==> (forall e :: e in this.edges ==> e !in t.edges) && (forall e :: e in t.edges ==> e !in this.edges)
  {
    t.nodes !! this.nodes && t.edges !! this.edges
  }

  lemma eq_exist_forall <T>(s: set<T>, w: set<T>)
    requires |s| == 1
    requires |w| > 0
    requires exists x :: x in s && x in w
    ensures forall x :: x in s ==> x in w

  lemma is_eq_tree_merge (t1: Tree, t2: Tree, e: Edge)
    requires t1.Valid() && t2.Valid()
    requires t1.IsDisjointComparedWith(t2)
    requires e !in t1.edges && e !in t2.edges
    requires |t1.edges| == |t1.nodes| - 1
    requires |t2.edges| == |t2.nodes| - 1
    requires IsSourceAndTargetPartOfDiffTrees(e,t1,t2)
    ensures forall node :: node in t1.nodes + t2.nodes ==> (exists edge :: edge in t1.edges + t2.edges + {e} && (node in {source(edge), target(edge)}))
  {
    assert |t1.edges| == |t1.nodes| - 1;
    assert |t2.edges| == |t2.nodes| - 1;
    if t1.edges == {} {
      if t2.edges == {} {
        var n1 :| n1 in t1.nodes; var n2 :| n2 in t2.nodes; var se: set<Edge> := {e}; var es: set<Node> := {source(e), target(e)} ;
        calc{
          |t2.edges| == 0 && |t2.nodes| == 1 && |t1.nodes| == 1 && |t1.edges| == 0 && n1 in t1.nodes && n2 in t2.nodes;
        ==> {}
          IsSourceAndTargetPartOfDiffTrees(e, t1, t2) ;
        ==> {}
          t1!=t2 && ((source(e) in t1.nodes && target(e) in t2.nodes) || (target(e) in t1.nodes && source(e) in t2.nodes)) ;
        ==> { assert t1 != t2 ; }
          ((source(e) in t1.nodes && target(e) in t2.nodes) || (target(e) in t1.nodes && source(e) in t2.nodes)) ;
        ==> { assert ((source(e) in t1.nodes || target(e) in t1.nodes) && (source(e) in t2.nodes || target(e) in t2.nodes)) ; }
          (exists no1 :: no1 in t1.nodes && no1 in es) && (exists no2:: no2 in t2.nodes && no2 in es);
        ==> { assert |t1.nodes| == 1 ; assert n1 in t1.nodes; eq_exist_forall(t1.nodes, es); eq_exist_forall(t2.nodes, es); }
          forall node :: node in t1.nodes + t2.nodes ==> node in es ;
        }
      }
      else {
        var es: set<Node> := {source(e), target(e)} ;
        calc {
          t1.Valid() && t2.Valid() && IsSourceAndTargetPartOfDiffTrees(e, t1, t2) ;
        ==> { assert |t1.edges| == 0 ; }
          |t1.nodes| == 1; && t1 != t2 && ((source(e) in t1.nodes && target(e) in t2.nodes) || (target(e) in t1.nodes && source(e) in t2.nodes)) ;
        ==> { assert t1 != t2 ; }
          ((source(e) in t1.nodes && target(e) in t2.nodes) || (target(e) in t1.nodes && source(e) in t2.nodes)) ;
        ==> {}
          exists no1:: no1 in t1.nodes && no1 in es;
        ==> {
              assert |t1.nodes| == 1;
              assert forall node :: node in t2.nodes ==> (exists edge :: edge in t2.edges && (node in {source(edge), target(edge)})) ;
              eq_exist_forall(t1.nodes, es);
              assert forall node :: node in t1.nodes ==> node in es ;
            }
          forall node :: node in t1.nodes + t2.nodes ==> (exists edge :: edge in t2.edges + {e} && (node in {source(edge), target(edge)})) ;
        }
      }
    }
    else {
      if t2.edges == {} {
        if (t1.nodes == {}) {}
        else {
          var es: set<Node> := {source(e), target(e)} ;
          calc {
            t1.Valid() && t2.Valid() && IsSourceAndTargetPartOfDiffTrees(e, t1, t2) ;
          ==> { assert |t2.edges| == 0 ; }
            |t2.nodes| == 1; && t1 != t2 && ((source(e) in t1.nodes && target(e) in t2.nodes) || (target(e) in t1.nodes && source(e) in t2.nodes)) ;
          ==> { assert t1 != t2 ; }
            ((source(e) in t1.nodes && target(e) in t2.nodes) || (target(e) in t1.nodes && source(e) in t2.nodes)) ;
          ==> {}
            exists no2:: no2 in t1.nodes && no2 in es;
          ==> {
                assert |t2.nodes| == 1;
                assert forall node :: node in t1.nodes ==> (exists edge :: edge in t1.edges && (node in {source(edge), target(edge)})) ;
                eq_exist_forall(t2.nodes, es);
                assert forall node :: node in t2.nodes ==> node in es ;
              }
            forall node :: node in t1.nodes + t2.nodes ==> (exists edge :: edge in t1.edges + {e} && (node in {source(edge), target(edge)})) ;
          }
        }
      }
      else {}
    }
  }

  method MergeWith(t: Tree, e: Edge)
    modifies this
    requires t.Valid() && Valid()
    requires IsDisjointComparedWith(t)
    requires e !in t.edges && e !in edges
    requires (source(e) in t.nodes && source(e) !in nodes && target(e) in nodes && target(e) !in t.nodes) ||
             (source(e) in nodes && source(e) !in t.nodes && target(e) in t.nodes && target(e) !in nodes)
    requires this.edges !! t.edges
    ensures |this.nodes| == old(|this.nodes|) + |t.nodes|
    ensures |this.edges| == old(|this.edges|) + |t.edges| + 1
    ensures forall ed :: ed in old(this.edges) || ed in t.edges || ed == e <==> ed in this.edges
    ensures forall n :: n in old(this.nodes) || n in t.nodes <==>  n in this.nodes
    ensures Valid()
  {
    is_eq_tree_merge(this, t, e) ;
    var tNodes := t.nodes;
    var tEdges := t.edges;
    this.nodes := nodes + tNodes;
    this.edges := edges + tEdges + { e };
  }

  static predicate IsSourceAndTargetPartOfDiffTrees(e: Edge, t1: Tree, t2: Tree)
    reads t1, t2
  {
    t1 != t2 && ((source(e) in t1.nodes && target(e) in t2.nodes) || (target(e) in t1.nodes && source(e) in t2.nodes))
  }
}

class Forest {
  var graph: Graph
  var sortedEdges: array<Edge>
  var forest: set<Tree>

  ghost predicate Valid()
    reads this
    reads forest
    reads sortedEdges

  {
    (forall t1: Tree, t2: Tree :: t1 in forest && t2 in forest && t1 != t2 ==> t1.IsDisjointComparedWith(t2))
    && (forall i, j :: 0 <= i < j < this.sortedEdges.Length ==> weight(this.sortedEdges[i]) <= weight(this.sortedEdges[j]))
  }

  ghost predicate ValidAfterCreation()
    reads this
    reads forest
  {
    |nodes(graph)| == |this.forest| &&
    (forall t: Tree :: t in this.forest ==> |t.nodes| == 1) &&
    (forall t1: Tree, t2: Tree :: t1 in this.forest && t2 in this.forest ==> t1 != t2 && t1.IsDisjointComparedWith(t2))
  }

  constructor(graph: Graph)
    requires validGraph(graph)
    ensures this.Valid()
    ensures |edges(graph)| == this.sortedEdges.Length
  {
    var forest := {};
    var nodes := nodes(graph);
    var i := 0;
    var ns := nodes;
    while i < |ns|
      invariant |ns| == |nodes| + i
      invariant |forest| == i
      invariant forall t: Tree :: t in forest ==> |t.nodes| == 1 && |t.edges| == 0
      invariant forall t1: Tree, t2: Tree :: t1 in forest && t2 in forest && t1 != t2 ==> t1.IsDisjointComparedWith(t2)
    {
      var node :| node in nodes;
      nodes := nodes - { node };
      var tree := new Tree(node);

      assert forall n: Node :: n in nodes ==> n != node;
      assert forall t: Tree :: t in forest ==> t != tree && node !in t.nodes && t.nodes !! tree.nodes;

      forest := forest + { tree };

      assert exists t: Tree :: t in forest && t.nodes * tree.nodes != {};

      i := i + 1;
    }

    var edges := edges(graph);
    this.forest := forest;
    var edgesArray := SetToArray(edges);

    Quicksort(edgesArray, 0, edgesArray.Length);
    this.sortedEdges := edgesArray;
  }

  method MergeTree(t1: Tree, t2: Tree, edge: Edge)
    modifies this
    requires this.Valid()
    requires t1 in forest && t2 in forest && t1 != t2 && t1.Valid() && t2.Valid() && t1.IsDisjointComparedWith(t2)
    requires forall t :: t in this.forest ==> edge !in t.edges
    requires source(edge) in t1.nodes && source(edge) !in t2.nodes && target(edge) in t2.nodes && target(edge) !in t1.nodes
    ensures |forest| == old(|forest|) - 1
    ensures this.Valid()
  {
    var newForestSet := forest - { t1, t2 };
    var newTree := new Tree.Clone(t1);

    newTree.MergeWith(t2, edge);

    newForestSet := newForestSet + { newTree };

    assert forall t :: t in newForestSet && t != newTree ==> newTree.IsDisjointComparedWith(t);

    assert |newForestSet| == |forest| - 1;

    this.forest := newForestSet;
  }

  predicate IsSafe(e: Edge)
    reads this
    reads this.forest
    reads this.sortedEdges
    requires this.Valid()
    requires |this.forest| >= 2
  {
    exists t1 : Tree, t2 : Tree :: t1 in this.forest && t2 in this.forest && t1 != t2 && ((source(e) in t1.nodes && target(e) in t2.nodes) || (source(e) in t2.nodes && target(e) in t1.nodes))
  }
  by method {
    var forestCopy: array<Tree> := SetToArray(this.forest);
    var found := false;
    if forestCopy.Length > 1 {
      found := VerifyIfEdgeIsSafe(e, forestCopy);
    } else {
      found := false;
    }

    return found;
  }

  method VerifyIfEdgeIsSafe(e: Edge, forestCopy: array<Tree>) returns (found: bool)
    requires this.Valid()
    requires forestCopy.Length > 0
    requires forall t :: t in this.forest  ==> (exists w :: 0 <= w < forestCopy.Length && forestCopy[w] == t)
    requires forall i :: 0 <= i < forestCopy.Length ==> forestCopy[i] in this.forest
    ensures found <==> (exists t1 : Tree, t2 : Tree :: t1 in this.forest && t2 in this.forest && Tree.IsSourceAndTargetPartOfDiffTrees(e,t1,t2))
  {
    var i := 0;
    found := Tree.IsSourceAndTargetPartOfDiffTrees(e, forestCopy[0], forestCopy[0]);

    while (!found && i < forestCopy.Length)
      decreases forestCopy.Length - i
      invariant forall t :: t in this.forest  ==> (exists w :: 0 <= w < forestCopy.Length && forestCopy[w] == t)
      invariant this.Valid()
      invariant |this.forest| == old(|this.forest|)
      invariant 0 <= i <= forestCopy.Length
      invariant forall x :: 0 <= x < i ==> !Tree.IsSourceAndTargetPartOfDiffTrees(e, forestCopy[x], forestCopy[x])
      invariant found ==> exists x, y :: 0 <= x <= y < forestCopy.Length && Tree.IsSourceAndTargetPartOfDiffTrees(e, forestCopy[x], forestCopy[y]);
      invariant !found ==> (forall k :: 0 <= k < i ==> (forall p :: 0 <= p < forestCopy.Length ==> !Tree.IsSourceAndTargetPartOfDiffTrees(e, forestCopy[p], forestCopy[k])))
    {

      var j := i;
      found := CheckAgainstAllTrees(forestCopy, i, e);
      i := i + 1;
    }
  }

  method CheckAgainstAllTrees(forestCopy: array<Tree>, i: int, e: Edge) returns (found: bool)
    requires this.Valid()
    requires 0 <= i < forestCopy.Length
    requires forall t :: t in this.forest ==> exists p :: 0 <= p < forestCopy.Length && forestCopy[p] == t
    requires forall p :: 0 <= p < forestCopy.Length ==> exists t :: t in this.forest && forestCopy[p] == t
    ensures found ==> (exists t1 : Tree, t2 : Tree :: t1 in this.forest && t2 in this.forest && Tree.IsSourceAndTargetPartOfDiffTrees(e,t1,t2))
    ensures !found ==> forall p :: 0 <= p < forestCopy.Length ==> !Tree.IsSourceAndTargetPartOfDiffTrees(e, forestCopy[i], forestCopy[p])
  {
    var j := 0;
    found := Tree.IsSourceAndTargetPartOfDiffTrees(e, forestCopy[i], forestCopy[j]);

    while (!found && j < forestCopy.Length)
      decreases forestCopy.Length - j
      invariant 0 <= j <= forestCopy.Length
      invariant found == true ==> exists x, y :: 0 <= x <= y < forestCopy.Length && x != y && Tree.IsSourceAndTargetPartOfDiffTrees(e, forestCopy[x], forestCopy[y]);
      invariant found == false ==> forall x :: 0 <= x < j ==> !Tree.IsSourceAndTargetPartOfDiffTrees(e, forestCopy[i], forestCopy[x])
    {

      if (Tree.IsSourceAndTargetPartOfDiffTrees(e,forestCopy[i],forestCopy[j]))
      {
        found := true;
      }

      j := j + 1;
    }
  }

  method FindCheapestSafeEdge() returns (e: Edge)
    requires this.Valid()
    requires |this.forest| >= 2
    requires exists i :: 0 <= i < this.sortedEdges.Length && IsSafe(this.sortedEdges[i])
    ensures forall j :: 0 <= j < this.sortedEdges.Length && IsSafe(this.sortedEdges[j]) ==> weight(e) <= weight(this.sortedEdges[j])
  {
    var i := 0;

    while (!IsSafe(this.sortedEdges[i]))
      decreases this.sortedEdges.Length - i
      invariant 0 <= i < this.sortedEdges.Length
      invariant forall j :: 0 <= j < i ==> !IsSafe(this.sortedEdges[j])
    {
      i := i + 1;
    }

    e := this.sortedEdges[i];
  }

  method FindByNode(node: Node) returns (t : Tree)
    requires exists t : Tree :: t in this.forest && node in t.nodes
    ensures |this.forest| == old(|this.forest|)
    ensures t in this.forest
    ensures node in t.nodes
  {
    var forestCopy := SetToArray(this.forest);
    var i := 0;
    while (node !in forestCopy[i].nodes)
      decreases forestCopy.Length - i;
      invariant exists j :: i <= j < forestCopy.Length && node in forestCopy[j].nodes
    {
      i := i + 1;
    }

    t := forestCopy[i];
  }
}

function ArrayToSet<T>(a: array<T>, lo: int, hi: int): set<T>
  reads a
  requires 0 <= lo <= hi <= a.Length
{
  set i | lo <= i < hi :: a[i]
}

method Quicksort(arr: array<Edge>, from: int, to: int)
  requires 0 <= from <= arr.Length
  requires -1 <= to < arr.Length
  requires from <= to + 1
  requires from > 0 ==> forall i :: from <= i <= to ==> weight(arr[from - 1]) <= weight(arr[i])
  requires to < arr.Length - 1 ==> forall i :: from <= i <= to ==> weight(arr[i]) <= weight(arr[to + 1])
  ensures forall a, b :: from <= a <= b <= to ==> weight(arr[a]) <= weight(arr[b])
  ensures from > 0 ==> forall i :: from <= i <= to ==> weight(arr[from - 1]) <= weight(arr[i])
  ensures to < arr.Length - 1 ==> forall i :: from <= i <= to ==> weight(arr[i]) <= weight(arr[to + 1])
  ensures forall k :: 0 <= k < from ==> weight(arr[k]) == old(weight(arr[k]))
  ensures forall k :: to < k < arr.Length ==> weight(arr[k]) == old(weight(arr[k]))
  decreases to - from
  modifies arr
{
  if (from < to)
  {
    var m: int := Partition(arr, from, to);
    Quicksort(arr, from, m - 1);
    Quicksort(arr, m + 1, to);
  }
}


method Partition(arr: array<Edge>, from: int, to: int) returns (l: int)
  requires 0 <= from <= to < arr.Length
  requires from > 0 ==> forall i :: from <= i <= to ==> weight(arr[from - 1]) <= weight(arr[i])
  requires to < arr.Length - 1 ==> forall i :: from <= i <= to ==> weight(arr[i]) <= weight(arr[to + 1])
  ensures from <= l <= to
  ensures forall k :: from <= k < l ==> weight(arr[k]) < weight(arr[l])
  ensures forall k :: l < k <= to ==> weight(arr[k]) >= weight(arr[l])
  ensures forall k :: 0 <= k < from ==> weight(arr[k]) == old(weight(arr[k]))
  ensures forall k :: to < k < arr.Length ==> weight(arr[k]) == old(weight(arr[k]))
  ensures from > 0 ==> forall i :: from <= i <= to ==> weight(arr[from - 1]) <= weight(arr[i])
  ensures to < arr.Length - 1 ==> forall i :: from <= i <= to ==> weight(arr[i]) <= weight(arr[to + 1])
  modifies arr
{
  l := from;
  var r: int := to;
  var pivot: Edge := arr[from];

  while (l != r)
    invariant from <= l <= r <= to
    invariant weight(pivot) == weight(arr[l])
    invariant forall k :: from <= k < l ==> weight(arr[k]) < weight(pivot)
    invariant forall k :: r < k <= to ==> weight(arr[k]) >= weight(pivot)
    invariant forall k :: 0 <= k < from ==> weight(arr[k]) == old(weight(arr[k]))
    invariant forall k :: to < k < arr.Length ==> weight(arr[k]) == old(weight(arr[k]))
    invariant from > 0 ==> forall i :: from <= i <= to ==> weight(arr[from - 1]) <= weight(arr[i])
    invariant to < arr.Length - 1 ==> forall i :: from <= i <= to ==> weight(arr[i]) <= weight(arr[to + 1])
    decreases r - l
    modifies arr
  {
    if (weight(pivot) <= weight(arr[r]))
    {
      r := r - 1;
    }
    else
    {
      arr[l] := arr[r];
      arr[r] := arr[l + 1];

      arr[l + 1] := pivot;
      l := l + 1;
    }
  }
}

method SetToArray<T>(s: set<T>) returns (a: array<T>)
  ensures |s| == a.Length
  ensures s == ArrayToSet(a, 0, a.Length)
  ensures forall v :: v in s ==> exists i :: 0 <= i < a.Length && a[i] == v
{
  if |s| == 0 {
    return new T[0];
  }

  var x :| x in s;

  a := new T[|s|](_ => x);

  var i := 0;
  var t := s;
  while i < |s|
    invariant 0 <= i <= a.Length
    invariant |s| == |t| + i
    invariant s == t + ArrayToSet(a, 0, i)
  {
    label L:
    var y :| y in t;
    a[i] := y;
    assert forall j | 0 <= j < i :: old@L(a[j]) == a[j];
    t := t - {y};
    i := i + 1;
  }
}

method Kruskal(g: Graph) returns (t: Tree)
  requires validGraph(g)
  ensures t.Valid()
{
  var forest := new Forest(g);
  while (|forest.forest| > 1) invariant forest.Valid() modifies forest decreases |forest.forest|
  {
    var candidateEdge := forest.FindCheapestSafeEdge();
    var tree1 := forest.FindByNode(source(candidateEdge));
    var tree2 := forest.FindByNode(target(candidateEdge));
    forest.MergeTree(tree1, tree2, candidateEdge);
  }
  t :| t in forest.forest;
}