include "cusgr.mm"
include "wcel.mm"
include "cuhgr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "wn.mm"
include "wb.mm"
include "usgruhgr.mm"
include "vtxduhgr0edgnel.mm"
include "sylan.mm"

theorem vtxdusgr0edgnel
  let cD: class D
  let cU: class U
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cV: class V
  let vc: setvar c
  let vi: setvar i
  let vx: setvar x
  let vv: setvar v
  assume vtxdushgrfvedg.v: |- V = ( Vtx ` G )
  assume vtxdushgrfvedg.e: |- E = ( Edg ` G )
  assume vtxdushgrfvedg.d: |- D = ( VtxDeg ` G )

  disjoint E e
  disjoint G e
  disjoint U e
  disjoint V e
  disjoint E c
  disjoint E i
  disjoint c e
  disjoint c i
  disjoint e i
  disjoint G c
  disjoint G i
  disjoint G x
  disjoint c x
  disjoint e x
  disjoint i x
  disjoint U c
  disjoint U i
  disjoint U x
  disjoint V c
  disjoint V i
  disjoint V x
  disjoint G v
  disjoint i v
  disjoint U v
  disjoint V v
  assert |- ( ( G e. USGraph /\ U e. V ) -> ( ( D ` U ) = 0 <-> -. E. e e. E U e. e ) )

  proof
    cG
    cusgr
    wcel
    cG
    cuhgr
    wcel
    cU
    cV
    wcel
    cU
    cD
    cfv
    cc0
    wceq
    cU
    ve
    cv
    wcel
    ve
    cE
    wrex
    wn
    wb
    cG
    usgruhgr
    cD
    cU
    ve
    cE
    cG
    cV
    vtxdushgrfvedg.v
    vtxdushgrfvedg.e
    vtxdushgrfvedg.d
    vtxduhgr0edgnel
    sylan
end
