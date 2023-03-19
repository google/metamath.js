include "cusgr.mm"
include "wcel.mm"
include "cuspgr.mm"
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
include "wf1.mm"
include "wceq.mm"
include "eqid.mm"
include "isusgr.mm"
include "wss.mm"
include "wi.mm"
include "2re.mm"
include "eqlei2.mm"
include "a1i.mm"
include "ss2rabi.mm"
include "f1ss.mm"
include "mpan2.mm"
include "syl6bi.mm"
include "isuspgr.mm"
include "sylibrd.mm"
include "pm2.43i.mm"

theorem usgruspgr
  let cG: class G
  let vx: setvar x


  assert |- ( G e. USGraph -> G e. USPGraph )

  proof
    cG
    cusgr
    wcel
    #
    cG
    cuspgr
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
    #
    chash
    cfv
    #
    c2
    cle
    wbr
    #
    vx
    cG
    cvtx
    cfv
    #
    cpw
    c0
    csn
    cdif
    #
    crab
    #
    @2
    wf1
    #
    @1
    @0
    @0
    @3
    @5
    c2
    wceq
    #
    vx
    @8
    crab
    #
    @2
    wf1
    #
    @10
    vx
    cusgr
    @2
    cG
    @7
    @7
    eqid
    #
    @2
    eqid
    #
    isusgr
    @13
    @12
    @9
    wss
    @10
    @11
    @6
    vx
    @8
    @11
    @6
    wi
    @4
    @8
    wcel
    c2
    @5
    2re
    eqlei2
    a1i
    ss2rabi
    @3
    @12
    @9
    @2
    f1ss
    mpan2
    syl6bi
    vx
    cusgr
    @2
    cG
    @7
    @14
    @15
    isuspgr
    sylibrd
    pm2.43i
end
