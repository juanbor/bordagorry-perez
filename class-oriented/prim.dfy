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
    |this.edges| == |this.nodes| - 1
    && (|edges| == 0 || (forall node: Node :: node in nodes ==>  (exists edge :: edge in edges && (node in {source(edge), target(edge)}))))
  }

  ghost predicate Covers(t: Tree)
    reads this, t
  {
    t.nodes <= this.nodes
  }

  constructor(node: Node)
    ensures Valid()
    ensures |nodes| == 1
    ensures |edges| == 0
    ensures node in nodes
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

  static ghost predicate IsSourceAndTargetPartOfDiffTrees(e: Edge, t1: Tree, t2: Tree)
    reads t1, t2
  {
    t1 != t2 && ((source(e) in t1.nodes && target(e) in t2.nodes) || (target(e) in t1.nodes && source(e) in t2.nodes))
  }

  static method IsSourceAndTargetPartOfDiffTreesM(e: Edge, t1: Tree, t2: Tree) returns (re: bool)
    ensures re == true ==> Tree.IsSourceAndTargetPartOfDiffTrees(e,t1,t2)
    ensures re == false ==> !Tree.IsSourceAndTargetPartOfDiffTrees(e,t1,t2)
    ensures Tree.IsSourceAndTargetPartOfDiffTrees(e,t1,t2) ==> re == true
    ensures !Tree.IsSourceAndTargetPartOfDiffTrees(e,t1,t2) ==> re == false
  {
    re := t1 != t2 && ((source(e) in t1.nodes && target(e) in t2.nodes) || (target(e) in t1.nodes && source(e) in t2.nodes));
  }
}

class PrimTree {
  var graph: Graph
  var sortedEdges: array<Edge>
  var resultTree: Tree
  var pendingTreesOfOneNode: set<Tree>

  ghost predicate Valid()
    reads this
    reads resultTree
    reads pendingTreesOfOneNode
    reads sortedEdges

  {
    (forall t1: Tree :: t1 in pendingTreesOfOneNode && t1 != this.resultTree ==> t1.IsDisjointComparedWith(this.resultTree))
    && (forall i, j :: 0 <= i < j < this.sortedEdges.Length ==> weight(this.sortedEdges[i]) <= weight(this.sortedEdges[j]))
  }

  ghost predicate ValidAfterCreation()
    reads this
  {
    |nodes(graph)| == |this.pendingTreesOfOneNode| + 1
  }

  constructor(graph: Graph)
    requires validGraph(graph)
    ensures this.Valid()
    ensures this.ValidAfterCreation()
    ensures |edges(graph)| == this.sortedEdges.Length
  {
    var nodes := nodes(graph);
    var edges := edges(graph);
    var edgesArray := SetToArray(edges);
    Quicksort(edgesArray, 0, edgesArray.Length);
    this.sortedEdges := edgesArray;

    var n :| n in nodes;
    nodes := nodes - { n };
    var tree := new Tree(n);
    this.resultTree := tree;

    this.pendingTreesOfOneNode := {};
    while (nodes != {})
    {
      var np :| np in nodes;
      nodes := nodes - { np };
      var tree := new Tree(n);
      this.pendingTreesOfOneNode := this.pendingTreesOfOneNode + { tree };
    }
  }

  method MergeTree(t1: Tree, edge: Edge)
    modifies this
    requires this.Valid()
    requires t1 in pendingTreesOfOneNode && t1 != this.resultTree && t1.Valid() && this.resultTree.Valid() && t1.IsDisjointComparedWith(this.resultTree)
    requires edge !in t1.edges && edge !in this.resultTree.edges
    requires forall t :: t in this.pendingTreesOfOneNode ==> edge !in t.edges
    requires source(edge) in t1.nodes && source(edge) !in this.resultTree.nodes && target(edge) in this.resultTree.nodes && target(edge) !in t1.nodes
    ensures |this.pendingTreesOfOneNode| == old(|this.pendingTreesOfOneNode|) - 1
  {
    var newForestSet := pendingTreesOfOneNode - { t1 };
    var newTree := new Tree.Clone(t1);

    newTree.MergeWith(this.resultTree, edge);

    newForestSet := newForestSet;

    assert |newForestSet| == |pendingTreesOfOneNode| - 1;

    this.pendingTreesOfOneNode := newForestSet;
    this.resultTree := newTree;
  }

  predicate isSafe(e: Edge)
    reads this
    reads resultTree
    reads pendingTreesOfOneNode
    reads sortedEdges
    requires this.Valid()
    requires |this.pendingTreesOfOneNode| >= 1
  {
    exists t1 : Tree:: t1 in this.pendingTreesOfOneNode && Tree.IsSourceAndTargetPartOfDiffTrees(e, t1, this.resultTree)
  }
  by method {
    var pendingTreesCopy: array<Tree> := SetToArray(this.pendingTreesOfOneNode);

    var found := VerifyIfEdgeIsSafe(e, pendingTreesCopy);
    assert (found == true) ==> (exists t1 : Tree:: t1 in this.pendingTreesOfOneNode && Tree.IsSourceAndTargetPartOfDiffTrees(e, t1, this.resultTree));
    assert (found == false) ==> !(exists t1 : Tree:: t1 in this.pendingTreesOfOneNode && Tree.IsSourceAndTargetPartOfDiffTrees(e, t1, this.resultTree));

    return found;
  }

  method VerifyIfEdgeIsSafe(e: Edge, pendingTreesCopy: array<Tree>) returns (found: bool)
    requires this.Valid()
    requires pendingTreesCopy.Length >= 1
    requires forall t :: t in this.pendingTreesOfOneNode  ==> (exists w :: 0 <= w < pendingTreesCopy.Length && pendingTreesCopy[w] == t)
    requires forall i :: 0 <= i < pendingTreesCopy.Length ==> pendingTreesCopy[i] in this.pendingTreesOfOneNode    ensures (found == true) ==> (exists t1 : Tree:: t1 in this.pendingTreesOfOneNode && Tree.IsSourceAndTargetPartOfDiffTrees(e, t1, this.resultTree))
    ensures (found == false) ==> !(exists t1 : Tree:: t1 in this.pendingTreesOfOneNode && Tree.IsSourceAndTargetPartOfDiffTrees(e, t1, this.resultTree))
  {
    var sourceNode := source(e);
    var targetNode := target(e);
    found := false;

    if ((sourceNode in this.resultTree.nodes || targetNode in this.resultTree.nodes) && !(sourceNode in this.resultTree.nodes && targetNode in this.resultTree.nodes)) {
      found := CheckAgainstAllTrees(pendingTreesCopy, e);
    } else {
      found := false;
    }
  }

  method CheckAgainstAllTrees(pendingTreesCopy: array<Tree>, e: Edge) returns (found: bool)
    requires this.Valid()
    requires pendingTreesCopy.Length >= 1
    requires forall t :: t in this.pendingTreesOfOneNode ==> exists p :: 0 <= p < pendingTreesCopy.Length && pendingTreesCopy[p] == t
    requires forall i :: 0 <= i < pendingTreesCopy.Length ==> pendingTreesCopy[i] in this.pendingTreesOfOneNode
    ensures (found == true) ==> (exists t1 : Tree :: t1 in this.pendingTreesOfOneNode && Tree.IsSourceAndTargetPartOfDiffTrees(e,t1,this.resultTree))
    ensures (found == false) ==> forall p :: 0 <= p < pendingTreesCopy.Length ==> !Tree.IsSourceAndTargetPartOfDiffTrees(e, this.resultTree, pendingTreesCopy[p])
  {
    var j := 0;
    found := Tree.IsSourceAndTargetPartOfDiffTreesM(e, this.resultTree, pendingTreesCopy[j]);

    while (!found && j < pendingTreesCopy.Length)
      decreases pendingTreesCopy.Length - j
      invariant this.Valid()
      invariant |this.pendingTreesOfOneNode| == old(|this.pendingTreesOfOneNode|)
      invariant 0 <= j <= pendingTreesCopy.Length
      invariant found == true ==> exists x :: 0 <= x < pendingTreesCopy.Length && Tree.IsSourceAndTargetPartOfDiffTrees(e, this.resultTree, pendingTreesCopy[x]);
      invariant found == false ==> forall x :: 0 <= x < j ==> !Tree.IsSourceAndTargetPartOfDiffTrees(e, this.resultTree, pendingTreesCopy[x])
    {

      var isSourceAndTargetPartOfDiffTrees2 := Tree.IsSourceAndTargetPartOfDiffTreesM(e,this.resultTree,pendingTreesCopy[j]);
      if (isSourceAndTargetPartOfDiffTrees2)
      {
        found := true;
      }

      j := j + 1;
    }
  }

  method FindCheapestSafeEdge() returns (e: Edge)

    requires this.Valid()
    requires |this.pendingTreesOfOneNode| >= 1
    requires this.sortedEdges.Length > 0
    requires exists i :: 0 <= i < this.sortedEdges.Length && isSafe(this.sortedEdges[i])
    ensures forall j :: 0 <= j < this.sortedEdges.Length && isSafe(this.sortedEdges[j]) ==> weight(e) <= weight(this.sortedEdges[j])
  {
    var i := 0;

    while (!isSafe(this.sortedEdges[i]))
      decreases this.sortedEdges.Length - i
      invariant 0 <= i < this.sortedEdges.Length
      invariant forall j :: 0 <= j < i ==> !isSafe(this.sortedEdges[j])
    {
      i := i + 1;
    }
    e := this.sortedEdges[i];

    assert forall j :: 0 <= j < this.sortedEdges.Length && isSafe(this.sortedEdges[j]) ==> weight(e) <= weight(this.sortedEdges[j]);


  }

  method FindByNode(node: Node) returns (t : Tree)
    requires exists t : Tree :: t in this.pendingTreesOfOneNode && node in t.nodes
    ensures |this.pendingTreesOfOneNode| == old(|this.pendingTreesOfOneNode|)
    ensures t in this.pendingTreesOfOneNode
    ensures node in t.nodes
  {
    var forestCopy := SetToArray(this.pendingTreesOfOneNode);
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

method Prim(g: Graph) returns (t: Tree)
  requires validGraph(g)
  ensures t.Valid()
{
  var prim := new PrimTree(g);
  while (|prim.pendingTreesOfOneNode| > 1)
    modifies prim
    decreases |prim.pendingTreesOfOneNode|
    invariant prim.Valid()
  {
    var candidateEdge := prim.FindCheapestSafeEdge();
    var sourceNode := source(candidateEdge);
    var targetNode := target(candidateEdge);

    if (sourceNode in prim.resultTree.nodes)
    {
      var tree := prim.FindByNode(target(candidateEdge));
      prim.MergeTree(t, candidateEdge);
    } else {
      var tree := prim.FindByNode(source(candidateEdge));
      prim.MergeTree(t, candidateEdge);
    }
  }

  assert |prim.pendingTreesOfOneNode| == 0;
  t := prim.resultTree;
}
