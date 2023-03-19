include "cfusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cuvtx.mm"
include "cfv.mm"
include "cnbgr.mm"
include "co.mm"
include "chash.mm"
include "c1.mm"
include "cmin.mm"
include "wceq.mm"
include "wi.mm"
include "uvtxnm1nbgr.mm"
include "ex.mm"
include "adantr.mm"
include "nbusgrvtxm1uvtx.mm"
include "impbid.mm"

theorem uvtxnbvtxm1
  let cU: class U
  let cG: class G
  let cV: class V
  let vv: setvar v
  assume uvtxnm1nbgr.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FinUSGraph /\ U e. V ) -> ( U e. ( UnivVtx ` G ) <-> ( # ` ( G NeighbVtx U ) ) = ( ( # ` V ) - 1 ) ) )

  proof
    cG
    cfusgr
    wcel
    #
    cU
    cV
    wcel
    #
    wa
    cU
    cG
    cuvtx
    cfv
    wcel
    #
    cG
    cU
    cnbgr
    co
    chash
    cfv
    cV
    chash
    cfv
    c1
    cmin
    co
    wceq
    #
    @0
    @2
    @3
    wi
    @1
    @0
    @2
    @3
    cG
    cU
    cV
    uvtxnm1nbgr.v
    uvtxnm1nbgr
    ex
    adantr
    cU
    cG
    cV
    uvtxnm1nbgr.v
    nbusgrvtxm1uvtx
    impbid
end
