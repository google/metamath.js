include "cv.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "wbr.mm"
include "wceq.mm"
include "bibi2i.mm"
include "albii.mm"
include "dfcleq.mm"
include "brtxpsd2.mm"
include "3bitr4ri.mm"

theorem brtxpsd3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cX: class X
  assume brtxpsd2.1: |- A e. _V
  assume brtxpsd2.2: |- B e. _V
  assume brtxpsd2.3: |- R = ( C \ ran ( ( _V (x) _E ) /_\ ( S (x) _V ) ) )
  assume brtxpsd2.4: |- A C B
  assume brtxpsd3.5: |- ( x e. X <-> x S A )

  disjoint X x
  disjoint A x
  disjoint B x
  disjoint S x
  assert |- ( A R B <-> B = X )

  proof
    vx
    cv
    #
    cB
    wcel
    #
    @0
    cX
    wcel
    #
    wb
    #
    vx
    wal
    @1
    @0
    cA
    cS
    wbr
    #
    wb
    #
    vx
    wal
    cB
    cX
    wceq
    cA
    cB
    cR
    wbr
    @3
    @5
    vx
    @2
    @4
    @1
    brtxpsd3.5
    bibi2i
    albii
    vx
    cB
    cX
    dfcleq
    vx
    cA
    cB
    cC
    cR
    cS
    brtxpsd2.1
    brtxpsd2.2
    brtxpsd2.3
    brtxpsd2.4
    brtxpsd2
    3bitr4ri
end
