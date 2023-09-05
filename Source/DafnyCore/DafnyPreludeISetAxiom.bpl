function TISet(Ty) : Ty;
axiom (forall t: Ty :: { TISet(t) } Inv0_TISet(TISet(t)) == t);
axiom (forall t: Ty :: { TISet(t) }     Tag(TISet(t))     == TagISet);

function Inv0_TISet(Ty) : Ty;

const unique TagISet    : TyTag;

axiom (forall bx : Box, t : Ty ::
    { $IsBox(bx, TISet(t)) }
    ( $IsBox(bx, TISet(t)) ==> $Box($Unbox(bx) : ISet) == bx && $Is($Unbox(bx) : ISet, TISet(t))));

axiom (forall v: ISet, t0: Ty :: { $Is(v, TISet(t0)) }
  $Is(v, TISet(t0)) <==>
  (forall bx: Box :: { v[bx] }
    v[bx] ==> $IsBox(bx, t0)));

#if USE_HEAP
axiom (forall v: ISet, t0: Ty, h: Heap :: { $IsAlloc(v, TISet(t0), h) }
  $IsAlloc(v, TISet(t0), h) <==>
  (forall bx: Box :: { v[bx] }
    v[bx] ==> $IsAllocBox(bx, t0, h)));
#endif
// ---------------------------------------------------------------
// -- Axiomatization of isets -------------------------------------
// ---------------------------------------------------------------

type ISet = [Box]bool;

function ISet#Empty(): Set;
axiom (forall o: Box :: { ISet#Empty()[o] } !ISet#Empty()[o]);

// the empty set could be of anything
//axiom (forall t: Ty :: { $Is(ISet#Empty() : [Box]bool, TISet(t)) } $Is(ISet#Empty() : [Box]bool, TISet(t)));


function ISet#UnionOne(ISet, Box): ISet;
axiom (forall a: ISet, x: Box, o: Box :: { ISet#UnionOne(a,x)[o] }
  ISet#UnionOne(a,x)[o] <==> o == x || a[o]);
axiom (forall a: ISet, x: Box :: { ISet#UnionOne(a, x) }
  ISet#UnionOne(a, x)[x]);
axiom (forall a: ISet, x: Box, y: Box :: { ISet#UnionOne(a, x), a[y] }
  a[y] ==> ISet#UnionOne(a, x)[y]);

function ISet#Union(ISet, ISet): ISet;
axiom (forall a: ISet, b: ISet, o: Box :: { ISet#Union(a,b)[o] }
  ISet#Union(a,b)[o] <==> a[o] || b[o]);
axiom (forall a, b: ISet, y: Box :: { ISet#Union(a, b), a[y] }
  a[y] ==> ISet#Union(a, b)[y]);
axiom (forall a, b: Set, y: Box :: { ISet#Union(a, b), b[y] }
  b[y] ==> ISet#Union(a, b)[y]);
axiom (forall a, b: ISet :: { ISet#Union(a, b) }
  ISet#Disjoint(a, b) ==>
    ISet#Difference(ISet#Union(a, b), a) == b &&
    ISet#Difference(ISet#Union(a, b), b) == a);

function ISet#Intersection(ISet, ISet): ISet;
axiom (forall a: ISet, b: ISet, o: Box :: { ISet#Intersection(a,b)[o] }
  ISet#Intersection(a,b)[o] <==> a[o] && b[o]);

axiom (forall a, b: ISet :: { ISet#Union(ISet#Union(a, b), b) }
  ISet#Union(ISet#Union(a, b), b) == ISet#Union(a, b));
axiom (forall a, b: Set :: { ISet#Union(a, ISet#Union(a, b)) }
  ISet#Union(a, ISet#Union(a, b)) == ISet#Union(a, b));
axiom (forall a, b: ISet :: { ISet#Intersection(ISet#Intersection(a, b), b) }
  ISet#Intersection(ISet#Intersection(a, b), b) == ISet#Intersection(a, b));
axiom (forall a, b: ISet :: { ISet#Intersection(a, ISet#Intersection(a, b)) }
  ISet#Intersection(a, ISet#Intersection(a, b)) == ISet#Intersection(a, b));


function ISet#Difference(ISet, ISet): ISet;
axiom (forall a: ISet, b: ISet, o: Box :: { ISet#Difference(a,b)[o] }
  ISet#Difference(a,b)[o] <==> a[o] && !b[o]);
axiom (forall a, b: ISet, y: Box :: { ISet#Difference(a, b), b[y] }
  b[y] ==> !ISet#Difference(a, b)[y] );

function ISet#Subset(ISet, ISet): bool;
axiom (forall a: ISet, b: ISet :: { ISet#Subset(a,b) }
  ISet#Subset(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] ==> b[o]));

function ISet#Equal(ISet, ISet): bool;
axiom (forall a: ISet, b: ISet :: { ISet#Equal(a,b) }
  ISet#Equal(a,b) <==> (forall o: Box :: {a[o]} {b[o]} a[o] <==> b[o]));
axiom (forall a: ISet, b: ISet :: { ISet#Equal(a,b) }  // extensionality axiom for sets
  ISet#Equal(a,b) ==> a == b);

function ISet#Disjoint(ISet, ISet): bool;
axiom (forall a: ISet, b: ISet :: { ISet#Disjoint(a,b) }
  ISet#Disjoint(a,b) <==> (forall o: Box :: {a[o]} {b[o]} !a[o] || !b[o]));
