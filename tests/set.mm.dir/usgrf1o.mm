include "cusgr.mm"
include "wcel.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "c2.mm"
include "wceq.mm"
include "cvtx.mm"
include "cpw.mm"
include "crab.mm"
include "wf1.mm"
include "crn.mm"
include "wf1o.mm"
include "eqid.mm"
include "usgrfs.mm"
include "f1f1orn.mm"
include "syl.mm"

theorem usgrf1o
  let cE: class E
  let cG: class G
  let vx: setvar x
  assume usgrf1o.e: |- E = ( iEdg ` G )


  assert |- ( G e. USGraph -> E : dom E -1-1-onto-> ran E )

  proof
    cG
    cusgr
    wcel
    cE
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
    cE
    wf1
    @0
    cE
    crn
    cE
    wf1o
    vx
    cE
    cG
    @1
    @1
    eqid
    usgrf1o.e
    usgrfs
    @0
    @2
    cE
    f1f1orn
    syl
end
