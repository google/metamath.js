include "cusgr.mm"
include "wcel.mm"
include "cvtx.mm"
include "cfv.mm"
include "ciedg.mm"
include "cop.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "wf1.mm"
include "eqid.mm"
include "usgrfs.mm"
include "cvv.mm"
include "wa.mm"
include "wb.mm"
include "fvex.mm"
include "pm3.2i.mm"
include "isusgrop.mm"
include "mp1i.mm"
include "mpbird.mm"

theorem usgrop
  let cG: class G
  let vx: setvar x


  assert |- ( G e. USGraph -> <. ( Vtx ` G ) , ( iEdg ` G ) >. e. USGraph )

  proof
    cG
    cusgr
    wcel
    #
    cG
    cvtx
    cfv
    #
    cG
    ciedg
    cfv
    #
    cop
    cusgr
    wcel
    #
    @2
    cdm
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    @1
    cpw
    crab
    @2
    wf1
    #
    vx
    @2
    cG
    @1
    @1
    eqid
    @2
    eqid
    usgrfs
    @1
    cvv
    wcel
    #
    @2
    cvv
    wcel
    #
    wa
    @3
    @4
    wb
    @0
    @5
    @6
    cG
    cvtx
    fvex
    cG
    ciedg
    fvex
    pm3.2i
    @2
    @1
    cvv
    cvv
    vx
    isusgrop
    mp1i
    mpbird
end
