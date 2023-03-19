include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "cv.mm"
include "cedg.mm"
include "crab.mm"
include "cvtxdg.mm"
include "eqid.mm"
include "nbedgusgr.mm"
include "vtxdusgrfvedg.mm"
include "eqtr4d.mm"

theorem hashnbusgrvd
  let cU: class U
  let cG: class G
  let cV: class V
  let ve: setvar e
  assume hashnbusgrvd.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. USGraph /\ U e. V ) -> ( # ` ( G NeighbVtx U ) ) = ( ( VtxDeg ` G ) ` U ) )

  proof
    cG
    cusgr
    wcel
    cU
    cV
    wcel
    wa
    cG
    cU
    cnbgr
    co
    chash
    cfv
    cU
    ve
    cv
    wcel
    ve
    cG
    cedg
    cfv
    #
    crab
    chash
    cfv
    cU
    cG
    cvtxdg
    cfv
    #
    cfv
    cU
    ve
    @0
    cG
    cV
    hashnbusgrvd.v
    @0
    eqid
    #
    nbedgusgr
    @1
    cU
    ve
    @0
    cG
    cV
    hashnbusgrvd.v
    @2
    @1
    eqid
    vtxdusgrfvedg
    eqtr4d
end
