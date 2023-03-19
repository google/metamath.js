include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "ciedg.mm"
include "cdm.mm"
include "crab.mm"
include "chash.mm"
include "eqid.mm"
include "vtxdusgrval.mm"
include "cushgr.mm"
include "wceq.mm"
include "cuspgr.mm"
include "usgruspgr.mm"
include "uspgrushgr.mm"
include "syl.mm"
include "vtxdushgrfvedglem.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem vtxdusgrfvedg
  let cD: class D
  let cU: class U
  let ve: setvar e
  let cE: class E
  let cG: class G
  let cV: class V
  let vc: setvar c
  let vi: setvar i
  let vx: setvar x
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
  assert |- ( ( G e. USGraph /\ U e. V ) -> ( D ` U ) = ( # ` { e e. E | U e. e } ) )

  proof
    cG
    cusgr
    wcel
    #
    cU
    cV
    wcel
    #
    wa
    cU
    cD
    cfv
    cU
    vi
    cv
    cG
    ciedg
    cfv
    #
    cfv
    wcel
    vi
    @2
    cdm
    #
    crab
    chash
    cfv
    #
    cU
    ve
    cv
    wcel
    ve
    cE
    crab
    chash
    cfv
    #
    vi
    @3
    cD
    cU
    cG
    @2
    cV
    vtxdushgrfvedg.v
    @2
    eqid
    @3
    eqid
    vtxdushgrfvedg.d
    vtxdusgrval
    @0
    cG
    cushgr
    wcel
    #
    @1
    @4
    @5
    wceq
    @0
    cG
    cuspgr
    wcel
    @6
    cG
    usgruspgr
    cG
    uspgrushgr
    syl
    cU
    ve
    vi
    cE
    cG
    cV
    vtxdushgrfvedg.v
    vtxdushgrfvedg.e
    vtxdushgrfvedglem
    sylan
    eqtrd
end
