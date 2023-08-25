function TISet(Ty) : Ty;
axiom (forall t: Ty :: { TISet(t) } Inv0_TISet(TISet(t)) == t);
axiom (forall t: Ty :: { TISet(t) }     Tag(TISet(t))     == TagISet);

function Inv0_TISet(Ty) : Ty;

const unique TagISet     : TyTag;

axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TISet(t)) }
    ( $IsBox(bx, TISet(t)) ==> $Box($Unbox(bx) : ISet Box) == bx && $Is($Unbox(bx) : ISet Box, TISet(t))));

axiom (forall v: ISet Box, t0: Ty :: { $Is(v, TISet(t0)) }
  $Is(v, TISet(t0)) <==>
  (forall bx: Box :: { v[bx] }
    v[bx] ==> $IsBox(bx, t0)));

axiom (forall v: ISet Box, t0: Ty, h: Heap :: { $IsAlloc(v, TISet(t0), h) }
  $IsAlloc(v, TISet(t0), h) <==>
  (forall bx: Box :: { v[bx] }
    v[bx] ==> $IsAllocBox(bx, t0, h)));

// ---------------------------------------------------------------
// -- Axiomatization of isets -------------------------------------
// ---------------------------------------------------------------

type ISet T = [T]bool;

function ISet#Empty<T>(): Set T;
axiom (forall<T> o: T :: { ISet#Empty()[o] } !ISet#Empty()[o]);

// the empty set could be of anything
//axiom (forall<T> t: Ty :: { $Is(ISet#Empty() : [T]bool, TISet(t)) } $Is(ISet#Empty() : [T]bool, TISet(t)));


function ISet#UnionOne<T>(ISet T, T): ISet T;
axiom (forall<T> a: ISet T, x: T, o: T :: { ISet#UnionOne(a,x)[o] }
  ISet#UnionOne(a,x)[o] <==> o == x || a[o]);
axiom (forall<T> a: ISet T, x: T :: { ISet#UnionOne(a, x) }
  ISet#UnionOne(a, x)[x]);
axiom (forall<T> a: ISet T, x: T, y: T :: { ISet#UnionOne(a, x), a[y] }
  a[y] ==> ISet#UnionOne(a, x)[y]);

function ISet#Union<T>(ISet T, ISet T): ISet T;
axiom (forall<T> a: ISet T, b: ISet T, o: T :: { ISet#Union(a,b)[o] }
  ISet#Union(a,b)[o] <==> a[o] || b[o]);
axiom (forall<T> a, b: ISet T, y: T :: { ISet#Union(a, b), a[y] }
  a[y] ==> ISet#Union(a, b)[y]);
axiom (forall<T> a, b: Set T, y: T :: { ISet#Union(a, b), b[y] }
  b[y] ==> ISet#Union(a, b)[y]);
axiom (forall<T> a, b: ISet T :: { ISet#Union(a, b) }
  ISet#Disjoint(a, b) ==>
    ISet#Difference(ISet#Union(a, b), a) == b &&
    ISet#Difference(ISet#Union(a, b), b) == a);

function ISet#Intersection<T>(ISet T, ISet T): ISet T;
axiom (forall<T> a: ISet T, b: ISet T, o: T :: { ISet#Intersection(a,b)[o] }
  ISet#Intersection(a,b)[o] <==> a[o] && b[o]);

axiom (forall<T> a, b: ISet T :: { ISet#Union(ISet#Union(a, b), b) }
  ISet#Union(ISet#Union(a, b), b) == ISet#Union(a, b));
axiom (forall<T> a, b: Set T :: { ISet#Union(a, ISet#Union(a, b)) }
  ISet#Union(a, ISet#Union(a, b)) == ISet#Union(a, b));
axiom (forall<T> a, b: ISet T :: { ISet#Intersection(ISet#Intersection(a, b), b) }
  ISet#Intersection(ISet#Intersection(a, b), b) == ISet#Intersection(a, b));
axiom (forall<T> a, b: ISet T :: { ISet#Intersection(a, ISet#Intersection(a, b)) }
  ISet#Intersection(a, ISet#Intersection(a, b)) == ISet#Intersection(a, b));


function ISet#Difference<T>(ISet T, ISet T): ISet T;
axiom (forall<T> a: ISet T, b: ISet T, o: T :: { ISet#Difference(a,b)[o] }
  ISet#Difference(a,b)[o] <==> a[o] && !b[o]);
axiom (forall<T> a, b: ISet T, y: T :: { ISet#Difference(a, b), b[y] }
  b[y] ==> !ISet#Difference(a, b)[y] );

function ISet#Subset<T>(ISet T, ISet T): bool;
axiom (forall<T> a: ISet T, b: ISet T :: { ISet#Subset(a,b) }
  ISet#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));

function ISet#Equal<T>(ISet T, ISet T): bool;
axiom (forall<T> a: ISet T, b: ISet T :: { ISet#Equal(a,b) }
  ISet#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom (forall<T> a: ISet T, b: ISet T :: { ISet#Equal(a,b) }  // extensionality axiom for sets
  ISet#Equal(a,b) ==> a == b);

function ISet#Disjoint<T>(ISet T, ISet T): bool;
axiom (forall<T> a: ISet T, b: ISet T :: { ISet#Disjoint(a,b) }
  ISet#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));
