include "cusgr.mm"
include "wcel.mm"
include "cumgr.mm"
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
include "wf.mm"
include "wf1.mm"
include "eqid.mm"
include "usgrfs.mm"
include "f1f.mm"
include "syl.mm"
include "isumgrs.mm"
include "mpbird.mm"

theorem usgrumgr
  let cG: class G
  let vx: setvar x


  assert |- ( G e. USGraph -> G e. UMGraph )

  proof
    cG
    cusgr
    wcel
    #
    cG
    cumgr
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
    @1
    wf
    #
    @0
    @2
    @4
    @1
    wf1
    @5
    vx
    @1
    cG
    @3
    @3
    eqid
    #
    @1
    eqid
    #
    usgrfs
    @2
    @4
    @1
    f1f
    syl
    vx
    cusgr
    @1
    cG
    @3
    @6
    @7
    isumgrs
    mpbird
end
