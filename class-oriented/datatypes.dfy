datatype Weight = W(int)
datatype Node = V(int)

datatype Edge = Edge(Node, Node, Weight)
datatype Graph = Graph(set<Node>, set<Edge>)

function weight(e: Edge): int
{
  match e
  case Edge(s, t, W(w)) => w
}

function source(e: Edge): Node
{
  match e
  case Edge(s, t, w) => s
}

function target(e: Edge): Node
{
  match e
  case Edge(s, t, w) => t
}

function nodes(g: Graph): set<Node>
{
  match g
  case Graph(v, e) => v
}

function edges(g: Graph): set<Edge>
{
  match g
  case Graph(v, e) => e
}

function getNodes(g: Graph): set<Node>
{
  nodes(g)
}

function getEdges(g: Graph): set<Edge>
{
  edges(g)
}

