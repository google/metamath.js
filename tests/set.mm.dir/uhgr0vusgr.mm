include "cuhgr.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "cedg.mm"
include "ciedg.mm"
include "eqid.mm"
include "uhgr0v0e.mm"
include "wb.mm"
include "uhgriedg0edg0.mm"
include "adantr.mm"
include "mpbid.mm"
include "usgr0e.mm"

theorem uhgr0vusgr
  let cG: class G


  assert |- ( ( G e. UHGraph /\ ( Vtx ` G ) = (/) ) -> G e. USGraph )

  proof
    cG
    cuhgr
    wcel
    #
    cG
    cvtx
    cfv
    #
    c0
    wceq
    #
    wa
    #
    cG
    cuhgr
    @0
    @2
    simpl
    @3
    cG
    cedg
    cfv
    #
    c0
    wceq
    #
    cG
    ciedg
    cfv
    c0
    wceq
    #
    @4
    cG
    @1
    @1
    eqid
    @4
    eqid
    uhgr0v0e
    @0
    @5
    @6
    wb
    @2
    cG
    uhgriedg0edg0
    adantr
    mpbid
    usgr0e
end
