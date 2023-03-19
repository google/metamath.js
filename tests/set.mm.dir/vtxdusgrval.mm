include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
include "cfv.mm"
include "cv.mm"
include "crab.mm"
include "chash.mm"
include "wceq.mm"
include "usgrumgr.mm"
include "vtxdumgrval.mm"
include "sylan.mm"

theorem vtxdusgrval
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cU: class U
  let cG: class G
  let cI: class I
  let cV: class V
  assume vtxdlfgrval.v: |- V = ( Vtx ` G )
  assume vtxdlfgrval.i: |- I = ( iEdg ` G )
  assume vtxdlfgrval.a: |- A = dom I
  assume vtxdlfgrval.d: |- D = ( VtxDeg ` G )

  disjoint A x
  disjoint G x
  disjoint I x
  disjoint U x
  disjoint V x
  assert |- ( ( G e. USGraph /\ U e. V ) -> ( D ` U ) = ( # ` { x e. A | U e. ( I ` x ) } ) )

  proof
    cG
    cusgr
    wcel
    cG
    cumgr
    wcel
    cU
    cV
    wcel
    cU
    cD
    cfv
    cU
    vx
    cv
    cI
    cfv
    wcel
    vx
    cA
    crab
    chash
    cfv
    wceq
    cG
    usgrumgr
    vx
    cA
    cD
    cU
    cG
    cI
    cV
    vtxdlfgrval.v
    vtxdlfgrval.i
    vtxdlfgrval.a
    vtxdlfgrval.d
    vtxdumgrval
    sylan
end
