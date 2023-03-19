include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cusgr.mm"
include "ciedg.mm"
include "cuhgr.mm"
include "usgruhgr.mm"
include "uhgr0vb.mm"
include "syl5ib.mm"
include "wi.mm"
include "simpl.mm"
include "simpr.mm"
include "usgr0e.mm"
include "ex.mm"
include "adantr.mm"
include "impbid.mm"

theorem usgr0vb
  let cG: class G
  let cW: class W


  assert |- ( ( G e. W /\ ( Vtx ` G ) = (/) ) -> ( G e. USGraph <-> ( iEdg ` G ) = (/) ) )

  proof
    cG
    cW
    wcel
    #
    cG
    cvtx
    cfv
    c0
    wceq
    #
    wa
    #
    cG
    cusgr
    wcel
    #
    cG
    ciedg
    cfv
    c0
    wceq
    #
    @3
    cG
    cuhgr
    wcel
    @2
    @4
    cG
    usgruhgr
    cG
    cW
    uhgr0vb
    syl5ib
    @0
    @4
    @3
    wi
    @1
    @0
    @4
    @3
    @0
    @4
    wa
    cG
    cW
    @0
    @4
    simpl
    @0
    @4
    simpr
    usgr0e
    ex
    adantr
    impbid
end
