function TIMap(Ty, Ty) : Ty;
axiom (forall t, u: Ty :: { TIMap(t,u) } Inv0_TIMap(TIMap(t,u)) == t);
axiom (forall t, u: Ty :: { TIMap(t,u) } Inv1_TIMap(TIMap(t,u)) == u);
axiom (forall t, u: Ty :: { TIMap(t,u) } Tag(TIMap(t,u)) == TagIMap);

function Inv0_TIMap(Ty) : Ty;
function Inv1_TIMap(Ty) : Ty;

const unique TagIMap     : TyTag;

axiom (forall bx : Box, s : Ty, t : Ty ::
    { $IsBox(bx, TIMap(s, t)) }
    ( $IsBox(bx, TIMap(s, t)) ==> $Box($Unbox(bx) : IMap Box Box) == bx && $Is($Unbox(bx) : IMap Box Box, TIMap(s, t))));

axiom (forall v: IMap Box Box, t0: Ty, t1: Ty ::
  { $Is(v, TIMap(t0, t1)) }
  $Is(v, TIMap(t0, t1))
     <==> (forall bx: Box ::
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] }
      IMap#Domain(v)[bx] ==>
        $IsBox(IMap#Elements(v)[bx], t1) &&
        $IsBox(bx, t0)));
axiom (forall v: IMap Box Box, t0: Ty, t1: Ty ::
  { $Is(v, TIMap(t0, t1)) }
  $Is(v, TIMap(t0, t1)) ==>
    $Is(IMap#Domain(v), TISet(t0)) &&
    $Is(IMap#Values(v), TISet(t1)) &&
    $Is(IMap#Items(v), TISet(Tclass._System.Tuple2(t0, t1))));
axiom (forall v: IMap Box Box, t0: Ty, t1: Ty, h: Heap ::
  { $IsAlloc(v, TIMap(t0, t1), h) }
  $IsAlloc(v, TIMap(t0, t1), h)
     <==> (forall bx: Box ::
      { IMap#Elements(v)[bx] } { IMap#Domain(v)[bx] }
      IMap#Domain(v)[bx] ==>
        $IsAllocBox(IMap#Elements(v)[bx], t1, h) &&
        $IsAllocBox(bx, t0, h)));


// ---------------------------------------------------------------
// -- Axiomatization of IMaps ------------------------------------
// ---------------------------------------------------------------

type IMap U V;

// A IMap is defined by two functions, Map#Domain and Map#Elements.

function IMap#Domain<U,V>(IMap U V) : Set U;

function IMap#Elements<U,V>(IMap U V) : [U]V;

axiom (forall<U, V> m: IMap U V ::
  { IMap#Domain(m) }
  m == IMap#Empty() || (exists k: U :: IMap#Domain(m)[k]));
axiom (forall<U, V> m: IMap U V ::
  { IMap#Values(m) }
  m == IMap#Empty() || (exists v: V :: IMap#Values(m)[v]));
axiom (forall<U, V> m: IMap U V ::
  { IMap#Items(m) }
  m == IMap#Empty() || (exists k, v: Box :: IMap#Items(m)[$Box(#_System._tuple#2._#Make2(k, v))]));

axiom (forall<U, V> m: IMap U V ::
  { IMap#Domain(m) }
  m == IMap#Empty() <==> IMap#Domain(m) == ISet#Empty());
axiom (forall<U, V> m: IMap U V ::
  { IMap#Values(m) }
  m == IMap#Empty() <==> IMap#Values(m) == ISet#Empty());
axiom (forall<U, V> m: IMap U V ::
  { IMap#Items(m) }
  m == IMap#Empty() <==> IMap#Items(m) == ISet#Empty());

// The set of Values of a IMap can be obtained by the function IMap#Values, which is
// defined as follows.  Remember, a ISet is defined by membership (using Boogie's
// square brackets) so we need to define what these mean for the Set
// returned by Map#Values.

function IMap#Values<U,V>(IMap U V) : Set V;

axiom (forall<U,V> m: IMap U V, v: V :: { IMap#Values(m)[v] }
  IMap#Values(m)[v] ==
	(exists u: U :: { IMap#Domain(m)[u] } { IMap#Elements(m)[u] }
	  IMap#Domain(m)[u] &&
    v == IMap#Elements(m)[u]));

// The set of Items--that is, (key,value) pairs--of a Map can be obtained by the
// function IMap#Items.
// Everywhere else in this axiomatization, IMap is parameterized by types U V,
// even though Dafny only ever instantiates U V with Box Box.  This makes the
// axiomatization more generic.  Function IMap#Items, however, returns a set of
// pairs, and the axiomatization of pairs is Dafny specific.  Therefore, the
// definition of IMap#Items here is to be considered Dafny specific.  Also, note
// that it relies on the two destructors for 2-tuples.

function IMap#Items<U,V>(IMap U V) : Set Box;

axiom (forall m: IMap Box Box, item: Box :: { IMap#Items(m)[item] }
  IMap#Items(m)[item] <==>
    IMap#Domain(m)[_System.Tuple2._0($Unbox(item))] &&
    IMap#Elements(m)[_System.Tuple2._0($Unbox(item))] == _System.Tuple2._1($Unbox(item)));

// Here are the operations that produce Map values.
function IMap#Empty<U, V>(): IMap U V;
axiom (forall<U, V> u: U ::
        { IMap#Domain(IMap#Empty(): IMap U V)[u] }
        !IMap#Domain(IMap#Empty(): IMap U V)[u]);

function IMap#Glue<U, V>([U] bool, [U]V, Ty): IMap U V;
axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
  { IMap#Domain(IMap#Glue(a, b, t)) }
  IMap#Domain(IMap#Glue(a, b, t)) == a);
axiom (forall<U, V> a: [U]bool, b: [U]V, t: Ty ::
  { IMap#Elements(IMap#Glue(a, b, t)) }
  IMap#Elements(IMap#Glue(a, b, t)) == b);
axiom (forall a: [Box]bool, b: [Box]Box, t0, t1: Ty ::
  { IMap#Glue(a, b, TIMap(t0, t1)) }
  // In the following line, no trigger needed, since the quantifier only gets used in negative contexts
  (forall bx: Box :: a[bx] ==> $IsBox(bx, t0) && $IsBox(b[bx], t1))
  ==>
  $Is(Map#Glue(a, b, TIMap(t0, t1)), TIMap(t0, t1)));

//Build is used in displays
function IMap#Build<U, V>(IMap U V, U, V): IMap U V;
/*axiom (forall<U, V> m: IMap U V, u: U, v: V ::
  { IMap#Domain(IMap#Build(m, u, v))[u] } { IMap#Elements(IMap#Build(m, u, v))[u] }
  IMap#Domain(IMap#Build(m, u, v))[u] && IMap#Elements(IMap#Build(m, u, v))[u] == v);*/

axiom (forall<U, V> m: IMap U V, u: U, u': U, v: V ::
  { IMap#Domain(IMap#Build(m, u, v))[u'] } { IMap#Elements(IMap#Build(m, u, v))[u'] }
  (u' == u ==> IMap#Domain(IMap#Build(m, u, v))[u'] &&
               IMap#Elements(IMap#Build(m, u, v))[u'] == v) &&
  (u' != u ==> IMap#Domain(IMap#Build(m, u, v))[u'] == IMap#Domain(m)[u'] &&
               IMap#Elements(IMap#Build(m, u, v))[u'] == IMap#Elements(m)[u']));

//equality for imaps
function IMap#Equal<U, V>(IMap U V, IMap U V): bool;
axiom (forall<U, V> m: IMap U V, m': IMap U V::
  { IMap#Equal(m, m') }
    IMap#Equal(m, m') <==> (forall u : U :: IMap#Domain(m)[u] == IMap#Domain(m')[u]) &&
                          (forall u : U :: IMap#Domain(m)[u] ==> IMap#Elements(m)[u] == IMap#Elements(m')[u]));
// extensionality
axiom (forall<U, V> m: IMap U V, m': IMap U V::
  { IMap#Equal(m, m') }
    IMap#Equal(m, m') ==> m == m');

// IMap operations
function IMap#Merge<U, V>(IMap U V, IMap U V): IMap U V;
axiom (forall<U, V> m: IMap U V, n: IMap U V ::
  { IMap#Domain(IMap#Merge(m, n)) }
  IMap#Domain(IMap#Merge(m, n)) == Set#Union(IMap#Domain(m), IMap#Domain(n)));
axiom (forall<U, V> m: IMap U V, n: IMap U V, u: U ::
  { IMap#Elements(IMap#Merge(m, n))[u] }
  IMap#Domain(IMap#Merge(m, n))[u] ==>
    (!IMap#Domain(n)[u] ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(m)[u]) &&
    (IMap#Domain(n)[u] ==> IMap#Elements(IMap#Merge(m, n))[u] == IMap#Elements(n)[u]));

function IMap#Subtract<U, V>(IMap U V, Set U): IMap U V;
axiom (forall<U, V> m: IMap U V, s: Set U ::
  { IMap#Domain(IMap#Subtract(m, s)) }
  IMap#Domain(IMap#Subtract(m, s)) == Set#Difference(IMap#Domain(m), s));
axiom (forall<U, V> m: IMap U V, s: Set U, u: U ::
  { IMap#Elements(IMap#Subtract(m, s))[u] }
  IMap#Domain(IMap#Subtract(m, s))[u] ==>
    IMap#Elements(IMap#Subtract(m, s))[u] == IMap#Elements(m)[u]);
