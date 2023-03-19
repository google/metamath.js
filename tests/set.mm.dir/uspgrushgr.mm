include "cuspgr.mm"
include "wcel.mm"
include "cushgr.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "wf1.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "eqid.mm"
include "isuspgr.mm"
include "wss.mm"
include "ssrab2.mm"
include "f1ss.mm"
include "mpan2.mm"
include "syl6bi.mm"
include "isushgr.mm"
include "sylibrd.mm"
include "pm2.43i.mm"

theorem uspgrushgr
  let cG: class G
  let vx: setvar x


  assert |- ( G e. USPGraph -> G e. USHGraph )

  proof
    cG
    cuspgr
    wcel
    #
    cG
    cushgr
    wcel
    #
    @0
    @0
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
    @2
    wf1
    #
    @1
    @0
    @0
    @3
    vx
    cv
    chash
    cfv
    c2
    cle
    wbr
    #
    vx
    @5
    crab
    #
    @2
    wf1
    #
    @6
    vx
    cuspgr
    @2
    cG
    @4
    @4
    eqid
    #
    @2
    eqid
    #
    isuspgr
    @9
    @8
    @5
    wss
    @6
    @7
    vx
    @5
    ssrab2
    @3
    @8
    @5
    @2
    f1ss
    mpan2
    syl6bi
    cuspgr
    @2
    cG
    @4
    @10
    @11
    isushgr
    sylibrd
    pm2.43i
end
