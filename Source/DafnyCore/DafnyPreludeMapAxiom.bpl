function TMap(Ty, Ty) : Ty;
axiom (forall t, u: Ty :: { TMap(t,u) } Inv0_TMap(TMap(t,u)) == t);
axiom (forall t, u: Ty :: { TMap(t,u) } Inv1_TMap(TMap(t,u)) == u);
axiom (forall t, u: Ty :: { TMap(t,u) } Tag(TMap(t,u)) == TagMap);

function Inv0_TMap(Ty) : Ty;
function Inv1_TMap(Ty) : Ty;

const unique TagMap      : TyTag;

axiom (forall bx : Box, s : Ty, t : Ty ::
    { $IsBox(bx, TMap(s, t)) }
    ( $IsBox(bx, TMap(s, t)) ==> $Box($Unbox(bx) : Map Box Box) == bx && $Is($Unbox(bx) : Map Box Box, TMap(s, t))));

axiom (forall v: Map Box Box, t0: Ty, t1: Ty ::
  { $Is(v, TMap(t0, t1)) }
  $Is(v, TMap(t0, t1))
     <==> (forall bx: Box ::
      { Map#Elements(v)[bx] } { Map#Domain(v)[bx] }
      Map#Domain(v)[bx] ==>
        $IsBox(Map#Elements(v)[bx], t1) &&
        $IsBox(bx, t0)));
            
axiom (forall v: Map Box Box, t0: Ty, t1: Ty ::
  { $Is(v, TMap(t0, t1)) }
  $Is(v, TMap(t0, t1)) ==>
    $Is(Map#Domain(v), TSet(t0)) &&
    $Is(Map#Values(v), TSet(t1)) &&
    $Is(Map#Items(v), TSet(Tclass._System.Tuple2(t0, t1))));

axiom (forall v: Map Box Box, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(v, TMap(t0, t1), h) }
  $IsAlloc(v, TMap(t0, t1), h)
     <==> (forall bx: Box ::
      { Map#Elements(v)[bx] } { Map#Domain(v)[bx] }
      Map#Domain(v)[bx] ==>
        $IsAllocBox(Map#Elements(v)[bx], t1, h) &&
        $IsAllocBox(bx, t0, h)));

// ---------------------------------------------------------------
// -- Axiomatization of Maps -------------------------------------
// ---------------------------------------------------------------

type Map U V;

// A Map is defined by three functions, Map#Domain, Map#Elements, and #Map#Card.

function Map#Domain<U,V>(Map U V) : Set U;

function Map#Elements<U,V>(Map U V) : [U]V;

function Map#Card<U,V>(Map U V) : int;

axiom (forall<U,V> m: Map U V :: { Map#Card(m) } 0 <= Map#Card(m));

axiom (forall<U, V> m: Map U V ::
  { Map#Card(m) }
  Map#Card(m) == 0 <==> m == Map#Empty());

axiom (forall<U, V> m: Map U V ::
  { Map#Domain(m) }
  m == Map#Empty() || (exists k: U :: Map#Domain(m)[k]));
axiom (forall<U, V> m: Map U V ::
  { Map#Values(m) }
  m == Map#Empty() || (exists v: V :: Map#Values(m)[v]));
axiom (forall<U, V> m: Map U V ::
  { Map#Items(m) }
  m == Map#Empty() || (exists k, v: Box :: Map#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall<U, V> m: Map U V ::
  { Set#Card(Map#Domain(m)) } { Map#Card(m) }
  Set#Card(Map#Domain(m)) == Map#Card(m));
axiom (forall<U, V> m: Map U V ::
  { Set#Card(Map#Values(m)) } { Map#Card(m) }
  Set#Card(Map#Values(m)) <= Map#Card(m));
axiom (forall<U, V> m: Map U V ::
  { Set#Card(Map#Items(m)) } { Map#Card(m) }
  Set#Card(Map#Items(m)) == Map#Card(m));

// The set of Values of a Map can be obtained by the function Map#Values, which is
// defined as follows.  Remember, a Set is defined by membership (using Boogie's
// square brackets) and Map#Card, so we need to define what these mean for the Set
// returned by Map#Values.

function Map#Values<U,V>(Map U V) : Set V;

axiom (forall<U,V> m: Map U V, v: V :: { Map#Values(m)[v] }
  Map#Values(m)[v] ==
	(exists u: U :: { Map#Domain(m)[u] } { Map#Elements(m)[u] }
	  Map#Domain(m)[u] &&
    v == Map#Elements(m)[u]));

// The set of Items--that is, (key,value) pairs--of a Map can be obtained by the
// function Map#Items.  Again, we need to define membership of Set#Card for this
// set.  Everywhere else in this axiomatization, Map is parameterized by types U V,
// even though Dafny only ever instantiates U V with Box Box.  This makes the
// axiomatization more generic.  Function Map#Items, however, returns a set of
// pairs, and the axiomatization of pairs is Dafny specific.  Therefore, the
// definition of Map#Items here is to be considered Dafny specific.  Also, note
// that it relies on the two destructors for 2-tuples.

function Map#Items<U,V>(Map U V) : Set Box;

function #_System._tuple#2._#Make2(Box, Box) : DatatypeType;
function _System.Tuple2._0(DatatypeType) : Box;
function _System.Tuple2._1(DatatypeType) : Box;

axiom (forall m: Map Box Box, item: Box :: { Map#Items(m)[item] }
  Map#Items(m)[item] <==>
    Map#Domain(m)[_System.Tuple2._0($Unbox(item))] &&
    Map#Elements(m)[_System.Tuple2._0($Unbox(item))] == _System.Tuple2._1($Unbox(item)));

// Here are the operations that produce Map values.

function Map#Empty<U, V>(): Map U V;
axiom (forall<U, V> u: U ::
        { Map#Domain(Map#Empty(): Map U V)[u] }
        !Map#Domain(Map#Empty(): Map U V)[u]);

function Map#Glue<U, V>([U]bool, [U]V, Ty): Map U V;
axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
  { Map#Domain(Map#Glue(a, b, t)) }
  Map#Domain(Map#Glue(a, b, t)) == a);
axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
  { Map#Elements(Map#Glue(a, b, t)) }
  Map#Elements(Map#Glue(a, b, t)) == b);
axiom (forall a: [Box]bool, b: [Box]Box, t0, t1: Ty ::
  { Map#Glue(a, b, TMap(t0, t1)) }
  // In the following line, no trigger needed, since the quantifier only gets used in negative contexts
  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
  ==>
  $Is(Map#Glue(a, b, TMap(t0, t1)), TMap(t0, t1)));


//Build is used in displays, and for map updates
function Map#Build<U, V>(Map U V, U, V): Map U V;
/*axiom (forall<U, V> m: Map U V, u: U, v: V ::
  { Map#Domain(Map#Build(m, u, v))[u] } { Map#Elements(Map#Build(m, u, v))[u] }
  Map#Domain(Map#Build(m, u, v))[u] && Map#Elements(Map#Build(m, u, v))[u] == v);*/

axiom (forall<U, V> m: Map U V, u: U, u': U, v: V ::
  { Map#Domain(Map#Build(m, u, v))[u'] } { Map#Elements(Map#Build(m, u, v))[u'] }
  (u' == u ==> Map#Domain(Map#Build(m, u, v))[u'] &&
               Map#Elements(Map#Build(m, u, v))[u'] == v) &&
  (u' != u ==> Map#Domain(Map#Build(m, u, v))[u'] == Map#Domain(m)[u'] &&
               Map#Elements(Map#Build(m, u, v))[u'] == Map#Elements(m)[u']));
axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }
  Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m));
axiom (forall<U, V> m: Map U V, u: U, v: V :: { Map#Card(Map#Build(m, u, v)) }
  !Map#Domain(m)[u] ==> Map#Card(Map#Build(m, u, v)) == Map#Card(m) + 1);

// Map operations
function Map#Merge<U, V>(Map U V, Map U V): Map U V;
axiom (forall<U, V> m: Map U V, n: Map U V ::
  { Map#Domain(Map#Merge(m, n)) }
  Map#Domain(Map#Merge(m, n)) == Set#Union(Map#Domain(m), Map#Domain(n)));
axiom (forall<U, V> m: Map U V, n: Map U V, u: U ::
  { Map#Elements(Map#Merge(m, n))[u] }
  Map#Domain(Map#Merge(m, n))[u] ==>
    (!Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(m)[u]) &&
    (Map#Domain(n)[u] ==> Map#Elements(Map#Merge(m, n))[u] == Map#Elements(n)[u]));

function Map#Subtract<U, V>(Map U V, Set U): Map U V;
axiom (forall<U, V> m: Map U V, s: Set U ::
  { Map#Domain(Map#Subtract(m, s)) }
  Map#Domain(Map#Subtract(m, s)) == Set#Difference(Map#Domain(m), s));
axiom (forall<U, V> m: Map U V, s: Set U, u: U ::
  { Map#Elements(Map#Subtract(m, s))[u] }
  Map#Domain(Map#Subtract(m, s))[u] ==>
    Map#Elements(Map#Subtract(m, s))[u] == Map#Elements(m)[u]);

//equality for maps
function Map#Equal<U, V>(Map U V, Map U V): bool;
axiom (forall<U, V> m: Map U V, m': Map U V::
  { Map#Equal(m, m') }
    Map#Equal(m, m') <==> (forall u : U :: Map#Domain(m)[u] == Map#Domain(m')[u]) &&
                          (forall u : U :: Map#Domain(m)[u] ==> Map#Elements(m)[u] == Map#Elements(m')[u]));
// extensionality
axiom (forall<U, V> m: Map U V, m': Map U V::
  { Map#Equal(m, m') }
    Map#Equal(m, m') ==> m == m');

function Map#Disjoint<U, V>(Map U V, Map U V): bool;
axiom (forall<U, V> m: Map U V, m': Map U V ::
  { Map#Disjoint(m, m') }
    Map#Disjoint(m, m') <==> (forall o: U :: {Map#Domain(m)[o]} {Map#Domain(m')[o]} !Map#Domain(m)[o] || !Map#Domain(m')[o]));
