include "cumgr.mm"
include "wcel.mm"
include "cuhgr.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "cpr.mm"
include "wrex.mm"
include "wn.mm"
include "umgruhgr.mm"
include "vtxduhgr0nedg.mm"
include "syl3an1.mm"

theorem vtxdumgr0nedg
  let vv: setvar v
  let cD: class D
  let cU: class U
  let cE: class E
  let cG: class G
  let cV: class V
  let vc: setvar c
  let ve: setvar e
  let vi: setvar i
  let vx: setvar x
  assume vtxdushgrfvedg.v: |- V = ( Vtx ` G )
  assume vtxdushgrfvedg.e: |- E = ( Edg ` G )
  assume vtxdushgrfvedg.d: |- D = ( VtxDeg ` G )

  disjoint G v
  disjoint U v
  disjoint V v
  disjoint E c
  disjoint E e
  disjoint E i
  disjoint c e
  disjoint c i
  disjoint e i
  disjoint G c
  disjoint G e
  disjoint G i
  disjoint G x
  disjoint c x
  disjoint e x
  disjoint i x
  disjoint U c
  disjoint U e
  disjoint U i
  disjoint U x
  disjoint V c
  disjoint V e
  disjoint V i
  disjoint V x
  disjoint i v
  assert |- ( ( G e. UMGraph /\ U e. V /\ ( D ` U ) = 0 ) -> -. E. v e. V { U , v } e. E )

  proof
    cG
    cumgr
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
    vv
    cv
    cpr
    cE
    wcel
    vv
    cV
    wrex
    wn
    cG
    umgruhgr
    vv
    cD
    cU
    cE
    cG
    cV
    vtxdushgrfvedg.v
    vtxdushgrfvedg.e
    vtxdushgrfvedg.d
    vtxduhgr0nedg
    syl3an1
end
