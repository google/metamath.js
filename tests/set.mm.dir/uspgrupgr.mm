include "cuspgr.mm"
include "wcel.mm"
include "cupgr.mm"
include "ciedg.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "cle.mm"
include "wbr.mm"
include "cvtx.mm"
include "cpw.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "crab.mm"
include "wf.mm"
include "wf1.mm"
include "eqid.mm"
include "isuspgr.mm"
include "f1f.mm"
include "syl6bi.mm"
include "isupgr.mm"
include "sylibrd.mm"
include "pm2.43i.mm"

theorem uspgrupgr
  let cG: class G
  let vx: setvar x


  assert |- ( G e. USPGraph -> G e. UPGraph )

  proof
    cG
    cuspgr
    wcel
    #
    cG
    cupgr
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
    vx
    cv
    chash
    cfv
    c2
    cle
    wbr
    vx
    cG
    cvtx
    cfv
    #
    cpw
    c0
    csn
    cdif
    crab
    #
    @2
    wf
    #
    @1
    @0
    @0
    @3
    @5
    @2
    wf1
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
    @3
    @5
    @2
    f1f
    syl6bi
    vx
    cuspgr
    @2
    cG
    @4
    @7
    @8
    isupgr
    sylibrd
    pm2.43i
end
