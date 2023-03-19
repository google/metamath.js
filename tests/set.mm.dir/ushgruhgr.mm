include "cushgr.mm"
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
include "wf1.mm"
include "eqid.mm"
include "ushgrf.mm"
include "f1f.mm"
include "syl.mm"
include "isuhgr.mm"
include "mpbird.mm"

theorem ushgruhgr
  let cG: class G


  assert |- ( G e. USHGraph -> G e. UHGraph )

  proof
    cG
    cushgr
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
    @4
    @1
    wf1
    @5
    @1
    cG
    @3
    @3
    eqid
    #
    @1
    eqid
    #
    ushgrf
    @2
    @4
    @1
    f1f
    syl
    cushgr
    @1
    cG
    @3
    @6
    @7
    isuhgr
    mpbird
end
