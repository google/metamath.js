include "cfusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cnbgr.mm"
include "co.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "wceq.mm"
include "cuvtx.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "nbgrssovtx.mm"
include "sseli.mm"
include "wne.mm"
include "eldifsn.mm"
include "wi.mm"
include "nbusgrvtxm1.mm"
include "imp.mm"
include "syl5bi.mm"
include "impbid2.mm"
include "eqrdv.mm"
include "wb.mm"
include "uvtxnbgrb.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "ex.mm"

theorem nbusgrvtxm1uvtx
  let cU: class U
  let cG: class G
  let cV: class V
  let vv: setvar v
  assume uvtxnm1nbgr.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FinUSGraph /\ U e. V ) -> ( ( # ` ( G NeighbVtx U ) ) = ( ( # ` V ) - 1 ) -> U e. ( UnivVtx ` G ) ) )

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
    #
    cG
    cU
    cnbgr
    co
    #
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
    cU
    cG
    cuvtx
    cfv
    wcel
    #
    @2
    @4
    wa
    #
    @5
    @3
    cV
    cU
    csn
    cdif
    #
    wceq
    #
    @6
    vv
    @3
    @7
    @6
    vv
    cv
    #
    @3
    wcel
    #
    @9
    @7
    wcel
    #
    @3
    @7
    @9
    cG
    cV
    cU
    uvtxnm1nbgr.v
    nbgrssovtx
    sseli
    @11
    @9
    cV
    wcel
    @9
    cU
    wne
    wa
    #
    @6
    @10
    @9
    cV
    cU
    eldifsn
    @2
    @4
    @12
    @10
    wi
    cU
    cG
    @9
    cV
    uvtxnm1nbgr.v
    nbusgrvtxm1
    imp
    syl5bi
    impbid2
    eqrdv
    @1
    @5
    @8
    wb
    @0
    @4
    cG
    cU
    cV
    uvtxnm1nbgr.v
    uvtxnbgrb
    ad2antlr
    mpbird
    ex
end
