// ---------------------------------------------------------------
// -- Axiomatization of Maps -------------------------------------
// ---------------------------------------------------------------

type Map;

function {:identity} LitMap(x: Map): Map { x }

// A Map is defined by three functions, Map#Domain, Map#Elements, and #Map#Card.

function Map#Domain(Map) : Set;

function Map#Elements(Map) : [Box]Box;

function Map#Card(Map) : int;

axiom (forall m: Map :: { Map#Card(m) } 0 <= Map#Card(m));

axiom (forall m: Map ::
  { Map#Card(m) }
  Map#Card(m) == 0 <==> m == Map#Empty());

axiom (forall m: Map ::
  { Map#Domain(m) }
  m == Map#Empty() || (exists k: Box :: Map#Domain(m)[k]));
axiom (forall m: Map ::
  { Map#Values(m) }
  m == Map#Empty() || (exists v: Box :: Map#Values(m)[v]));
axiom (forall m: Map ::
  { Map#Items(m) }
  m == Map#Empty() || (exists k, v: Box :: Map#Items(m)[BoxDatatype(#_System._tuple#2._#Make2(k, v))]));

axiom (forall m: Map ::
  { Set#Card(Map#Domain(m)) } { Map#Card(m) }
  Set#Card(Map#Domain(m)) == Map#Card(m));
axiom (forall m: Map ::
  { Set#Card(Map#Values(m)) } { Map#Card(m) }
  Set#Card(Map#Values(m)) <= Map#Card(m));
axiom (forall m: Map ::
  { Set#Card(Map#Items(m)) } { Map#Card(m) }
  Set#Card(Map#Items(m)) == Map#Card(m));

// The set of Values of a Map can be obtained by the function Map#Values, which is
// defined as follows.  Remember, a Set is defined by membership (using Boogie's
// square brackets) and Map#Card, so we need to define what these mean for the Set
// returned by Map#Values.

function Map#Values(Map) : Set;

axiom (forall m: Map, v: Box :: { Map#Values(m)[v] }
  Map#Values(m)[v] ==
	(exists u: Box :: { Map#Domain(m)[u] } { Map#Elements(m)[u] }
	  Map#Domain(m)[u] &&
    v == Map#Elements(m)[u]));

// The set of Items--that is, (key,value) pairs--of a Map can be obtained by the
// function Map#Items.  Again, we need to define membership of Set#Card for this
// set.  Everywhere else in this axiomatization, Map is parameterized by types Box V,
// even though Dafny only ever instantiates U V with Box Box.  This makes the
// axiomatization more generic.  Function Map#Items, however, returns a set of
// pairs, and the axiomatization of pairs is Dafny specific.  Therefore, the
// definition of Map#Items here is to be considered Dafny specific.  Also, note
// that it relies on the two destructors for 2-tuples.

function Map#Items(Map) : Set;

axiom (forall m: Map, item: Box :: { Map#Items(m)[item] }
  Map#Items(m)[item] <==>
    Map#Domain(m)[_System.Tuple2._0(item->vDatatype)] &&
    Map#Elements(m)[_System.Tuple2._0(item->vDatatype)] == _System.Tuple2._1(item->vDatatype));

// Here are the operations that produce Map values.

function Map#Empty(): Map;
axiom (forall u: Box ::
        { Map#Domain(Map#Empty(): Map)[u] }
        !Map#Domain(Map#Empty(): Map)[u]);

function Map#Glue([Box]bool, [Box]Box, Ty): Map;
axiom (forall a: [Box]bool, b: [Box]Box, t: Ty ::
  { Map#Domain(Map#Glue(a, b, t)) }
  Map#Domain(Map#Glue(a, b, t)) == a);
axiom (forall a: [Box]bool, b: [Box]Box, t: Ty ::
  { Map#Elements(Map#Glue(a, b, t)) }
  Map#Elements(Map#Glue(a, b, t)) == b);
// axiom (forall a: [Box]bool, b: [Box]Box, t0, t1: Ty ::
//   { Map#Glue(a, b, TMap(t0, t1)) }
//   // In the following line, no trigger needed, since the quantifier only gets used in negative contexts
//   (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
//   ==>
//   $Is(Map#Glue(a, b, TMap(t0, t1)), TMap(t0, t1)));


//Build is used in displays, and for map updates
function Map#Build(Map, Box, Box): Map;
/*axiom (forall m: Map, u: Box, v: Box ::
  { Map#Domain(Map#Build(m, u, v))[u] } { Map#Elements(Map#Build(m, u, v))[u] }
  Map#Domain(Map#Build(m, u, v))[u] && Map#Elements(Map#Build(m, u, v))[u] == v);*/

axiom (forall m: Map, u: Box, u': Box, v: Box ::
  { Map#Domain(Map#Build(m, u, v))[u'] } { Map#Elements(Map#Build(m, u, v))[u'] }
  (u' == u ==> Map#Domain(Map#Build(m, u, v))[u'] &&
               Map#Elements(Map#Build(m, u, v))[u'] == v) &&
  (u' != u ==> Map#Domain(Map#Build(m, u, v))[u'] == Map#Domain(m)[u'] &&
               Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));
axiom (forall m: Map, u: Box, v: Box :: { Map#Card(Map#Build(m, u, v)) }
  Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));
axiom (forall m: Map, u: Box, v: Box :: { Map#Card(Map#Build(m, u, v)) }
  !Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

// Map operations
function Map#Merge(Map, Map): Map;
axiom (forall m: Map, n: Map ::
  { Map#Domain(Map#Merge(m, n)) }
  Map#Domain(Map#Merge(m, n)) == Set#Union(Map#Domain(m), Map#Domain(n)));
axiom (forall m: Map, n: Map, u: Box ::
  { Map#Elements(Map#Merge(m, n))[u] }
  Map#Domain(Map#Merge(m, n))[u] ==>
    (!Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(m)[u]) &&
    (Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(n)[u]));

function Map#Subtract(Map, Set): Map;
axiom (forall m: Map, s: Set ::
  { Map#Domain(Map#Subtract(m, s)) }
  Map#Domain(Map#Subtract(m, s)) == Set#Difference(Map#Domain(m), s));
axiom (forall m: Map, s: Set, u: Box ::
  { Map#Elements(Map#Subtract(m, s))[u] }
  Map#Domain(Map#Subtract(m, s))[u] ==>
    Map#Elements(Map#Subtract(m, s))[u] == Map#Elements(m)[u]);

//equality for maps
function Map#Equal(Map, Map): bool;
axiom (forall m: Map, m': Map::
  { Map#Equal(m, m') }
    Map#Equal(m, m') <==> (forall u : Box :: Map#Domain(m)[u] == Map#Domain(m')[u]) &&
                          (forall u : Box :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]));
// extensionality
axiom (forall m: Map, m': Map::
  { Map#Equal(m, m') }
    Map#Equal(m, m') ==> m == m');

function Map#Disjoint(Map, Map): bool;
axiom (forall m: Map, m': Map ::
  { Map#Disjoint(m, m') }
    Map#Disjoint(m, m') <==> (forall o: Box :: {Map#Domain(m)[o]} {Map#Domain(m')[o]} !Map#Domain(m)[o] || !Map#Domain(m')[o]));
