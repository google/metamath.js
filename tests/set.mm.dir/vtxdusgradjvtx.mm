include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cvtxdg.mm"
include "cv.mm"
include "cpr.mm"
include "crab.mm"
include "hashnbusgrvd.mm"
include "wceq.mm"
include "nbusgr.mm"
include "adantr.mm"
include "fveq2d.mm"
include "eqtr3d.mm"

theorem vtxdusgradjvtx
  let vv: setvar v
  let cU: class U
  let cE: class E
  let cG: class G
  let cV: class V
  assume vtxdusgradjvtx.v: |- V = ( Vtx ` G )
  assume vtxdusgradjvtx.e: |- E = ( Edg ` G )

  disjoint E v
  disjoint G v
  disjoint U v
  disjoint V v
  assert |- ( ( G e. USGraph /\ U e. V ) -> ( ( VtxDeg ` G ) ` U ) = ( # ` { v e. V | { U , v } e. E } ) )

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
    #
    cG
    cU
    cnbgr
    co
    #
    chash
    cfv
    cU
    cG
    cvtxdg
    cfv
    cfv
    cU
    vv
    cv
    cpr
    cE
    wcel
    vv
    cV
    crab
    #
    chash
    cfv
    cU
    cG
    cV
    vtxdusgradjvtx.v
    hashnbusgrvd
    @2
    @3
    @4
    chash
    @0
    @3
    @4
    wceq
    @1
    vv
    cE
    cG
    cU
    cV
    vtxdusgradjvtx.v
    vtxdusgradjvtx.e
    nbusgr
    adantr
    fveq2d
    eqtr3d
end
