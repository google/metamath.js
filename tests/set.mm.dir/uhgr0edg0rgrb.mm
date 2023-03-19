include "cuhgr.mm"
include "wcel.mm"
include "cc0.mm"
include "crgr.mm"
include "wbr.mm"
include "cedg.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cxnn0.mm"
include "cv.mm"
include "cvtxdg.mm"
include "cvtx.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "eqid.mm"
include "uhgrvd00.mm"
include "com12.mm"
include "adantl.mm"
include "rgrprop.mm"
include "syl11.mm"
include "uhgr0edg0rgr.mm"
include "ex.mm"
include "impbid.mm"

theorem uhgr0edg0rgrb
  let cG: class G
  let vv: setvar v
  let cW: class W


  assert |- ( G e. UHGraph -> ( G RegGraph 0 <-> ( Edg ` G ) = (/) ) )

  proof
    cG
    cuhgr
    wcel
    #
    cG
    cc0
    crgr
    wbr
    #
    cG
    cedg
    cfv
    #
    c0
    wceq
    #
    cc0
    cxnn0
    wcel
    #
    vv
    cv
    cG
    cvtxdg
    cfv
    #
    cfv
    cc0
    wceq
    vv
    cG
    cvtx
    cfv
    #
    wral
    #
    wa
    @0
    @3
    @1
    @7
    @0
    @3
    wi
    @4
    @0
    @7
    @3
    vv
    @2
    cG
    @6
    @6
    eqid
    #
    @2
    eqid
    uhgrvd00
    com12
    adantl
    vv
    @5
    cG
    cc0
    @6
    @8
    @5
    eqid
    rgrprop
    syl11
    @0
    @3
    @1
    cG
    uhgr0edg0rgr
    ex
    impbid
end
