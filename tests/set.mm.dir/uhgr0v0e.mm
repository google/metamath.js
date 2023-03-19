include "cuhgr.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "ciedg.mm"
include "cfv.mm"
include "cvtx.mm"
include "wi.mm"
include "eqeq1i.mm"
include "uhgr0vb.mm"
include "biimpd.mm"
include "ex.mm"
include "syl5bi.mm"
include "pm2.43a.mm"
include "imp.mm"
include "wb.mm"
include "cedg.mm"
include "uhgriedg0edg0.mm"
include "syl5bb.mm"
include "adantr.mm"
include "mpbird.mm"

theorem uhgr0v0e
  let cE: class E
  let cG: class G
  let cV: class V
  assume uhgr0v0e.v: |- V = ( Vtx ` G )
  assume uhgr0v0e.e: |- E = ( Edg ` G )


  assert |- ( ( G e. UHGraph /\ V = (/) ) -> E = (/) )

  proof
    cG
    cuhgr
    wcel
    #
    cV
    c0
    wceq
    #
    wa
    cE
    c0
    wceq
    #
    cG
    ciedg
    cfv
    c0
    wceq
    #
    @0
    @1
    @3
    @1
    @0
    @3
    @1
    cG
    cvtx
    cfv
    #
    c0
    wceq
    #
    @0
    @0
    @3
    wi
    #
    cV
    @4
    c0
    uhgr0v0e.v
    eqeq1i
    @0
    @5
    @6
    @0
    @5
    wa
    @0
    @3
    cG
    cuhgr
    uhgr0vb
    biimpd
    ex
    syl5bi
    pm2.43a
    imp
    @0
    @2
    @3
    wb
    @1
    @2
    cG
    cedg
    cfv
    #
    c0
    wceq
    @0
    @3
    cE
    @7
    c0
    uhgr0v0e.e
    eqeq1i
    cG
    uhgriedg0edg0
    syl5bb
    adantr
    mpbird
end
