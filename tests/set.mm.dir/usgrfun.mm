include "cusgr.mm"
include "wcel.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "crab.mm"
include "wf1.mm"
include "wfun.mm"
include "eqid.mm"
include "usgrfs.mm"
include "f1fun.mm"
include "syl.mm"

theorem usgrfun
  let cG: class G
  let vx: setvar x


  assert |- ( G e. USGraph -> Fun ( iEdg ` G ) )

  proof
    cG
    cusgr
    wcel
    cG
    ciedg
    cfv
    #
    cdm
    #
    vx
    cv
    chash
    cfv
    c2
    wceq
    vx
    cG
    cvtx
    cfv
    #
    cpw
    crab
    #
    @0
    wf1
    @0
    wfun
    vx
    @0
    cG
    @2
    @2
    eqid
    @0
    eqid
    usgrfs
    @1
    @3
    @0
    f1fun
    syl
end
