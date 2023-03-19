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
include "cvtxdg.mm"
include "uvtxnbvtxm1.mm"
include "cusgr.mm"
include "fusgrusgr.mm"
include "hashnbusgrvd.mm"
include "sylan.mm"
include "eqeq1d.mm"
include "bitrd.mm"

theorem usgruvtxvdb
  let cU: class U
  let cG: class G
  let cV: class V
  let ve: setvar e
  assume hashnbusgrvd.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. FinUSGraph /\ U e. V ) -> ( U e. ( UnivVtx ` G ) <-> ( ( VtxDeg ` G ) ` U ) = ( ( # ` V ) - 1 ) ) )

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
    cU
    cG
    cuvtx
    cfv
    wcel
    cG
    cU
    cnbgr
    co
    chash
    cfv
    #
    cV
    chash
    cfv
    c1
    cmin
    co
    #
    wceq
    cU
    cG
    cvtxdg
    cfv
    cfv
    #
    @4
    wceq
    cU
    cG
    cV
    hashnbusgrvd.v
    uvtxnbvtxm1
    @2
    @3
    @5
    @4
    @0
    cG
    cusgr
    wcel
    @1
    @3
    @5
    wceq
    cG
    fusgrusgr
    cU
    cG
    cV
    hashnbusgrvd.v
    hashnbusgrvd
    sylan
    eqeq1d
    bitrd
end
