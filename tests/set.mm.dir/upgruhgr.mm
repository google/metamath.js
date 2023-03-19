include "cupgr.mm"
include "wcel.mm"
include "cuhgr.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "wss.mm"
include "eqid.mm"
include "upgrf.mm"
include "ssrab2.mm"
include "fss.mm"
include "sylancl.mm"
include "isuhgr.mm"
include "mpbird.mm"

theorem upgruhgr
  let cG: class G
  let vx: setvar x


  assert |- ( G e. UPGraph -> G e. UHGraph )

  proof
    cG
    cupgr
    wcel
    #
    cG
    cuhgr
    wcel
    cG
    ciedg
    cfv
    #
    cdm
    #
    cG
    cvtx
    cfv
    #
    cpw
    c0
    csn
    cdif
    #
    @1
    wf
    #
    @0
    @2
    vx
    cv
    chash
    cfv
    c2
    cle
    wbr
    #
    vx
    @4
    crab
    #
    @1
    wf
    @7
    @4
    wss
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
    upgrf
    @6
    vx
    @4
    ssrab2
    @2
    @7
    @4
    @1
    fss
    sylancl
    cupgr
    @1
    cG
    @3
    @8
    @9
    isuhgr
    mpbird
end
