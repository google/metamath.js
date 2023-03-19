include "cuhgr.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "wfun.mm"
include "cedg.mm"
include "c0.mm"
include "wceq.mm"
include "wb.mm"
include "eqid.mm"
include "uhgrfun.mm"
include "edg0iedg0.mm"
include "syl.mm"

theorem uhgriedg0edg0
  let cG: class G


  assert |- ( G e. UHGraph -> ( ( Edg ` G ) = (/) <-> ( iEdg ` G ) = (/) ) )

  proof
    cG
    cuhgr
    wcel
    cG
    ciedg
    cfv
    #
    wfun
    cG
    cedg
    cfv
    #
    c0
    wceq
    @0
    c0
    wceq
    wb
    @0
    cG
    @0
    eqid
    #
    uhgrfun
    @1
    cG
    @0
    @2
    @1
    eqid
    edg0iedg0
    syl
end
