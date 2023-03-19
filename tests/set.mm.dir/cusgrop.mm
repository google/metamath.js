include "cusgr.mm"
include "wcel.mm"
include "ccplgr.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "ciedg.mm"
include "cop.mm"
include "ccusgr.mm"
include "usgrop.mm"
include "cplgrop.mm"
include "anim12i.mm"
include "iscusgr.mm"
include "3imtr4i.mm"

theorem cusgrop
  let cG: class G


  assert |- ( G e. ComplUSGraph -> <. ( Vtx ` G ) , ( iEdg ` G ) >. e. ComplUSGraph )

  proof
    cG
    cusgr
    wcel
    #
    cG
    ccplgr
    wcel
    #
    wa
    cG
    cvtx
    cfv
    cG
    ciedg
    cfv
    cop
    #
    cusgr
    wcel
    #
    @2
    ccplgr
    wcel
    #
    wa
    cG
    ccusgr
    wcel
    @2
    ccusgr
    wcel
    @0
    @3
    @1
    @4
    cG
    usgrop
    cG
    cplgrop
    anim12i
    cG
    iscusgr
    @2
    iscusgr
    3imtr4i
end
