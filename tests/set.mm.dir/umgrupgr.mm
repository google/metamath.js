include "cumgr.mm"
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
include "wceq.mm"
include "eqid.mm"
include "isumgr.mm"
include "id.mm"
include "wss.mm"
include "wi.mm"
include "2re.mm"
include "leidi.mm"
include "a1i.mm"
include "breq1.mm"
include "mpbird.mm"
include "ss2rabi.mm"
include "fssd.mm"
include "syl6bi.mm"
include "pm2.43i.mm"
include "isupgr.mm"

theorem umgrupgr
  let cG: class G
  let vx: setvar x


  assert |- ( G e. UMGraph -> G e. UPGraph )

  proof
    cG
    cumgr
    wcel
    #
    cG
    cupgr
    wcel
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
    @1
    wf
    #
    @0
    @9
    @0
    @0
    @2
    @4
    c2
    wceq
    #
    vx
    @7
    crab
    #
    @1
    wf
    #
    @9
    vx
    cumgr
    @1
    cG
    @6
    @6
    eqid
    #
    @1
    eqid
    #
    isumgr
    @12
    @2
    @11
    @8
    @1
    @12
    id
    @11
    @8
    wss
    @12
    @10
    @5
    vx
    @7
    @10
    @5
    wi
    @3
    @7
    wcel
    @10
    @5
    c2
    c2
    cle
    wbr
    #
    @15
    @10
    c2
    2re
    leidi
    a1i
    @4
    c2
    c2
    cle
    breq1
    mpbird
    a1i
    ss2rabi
    a1i
    fssd
    syl6bi
    pm2.43i
    vx
    cumgr
    @1
    cG
    @6
    @13
    @14
    isupgr
    mpbird
end
