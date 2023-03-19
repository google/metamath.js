include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cutop.mm"
include "cuni.mm"
include "cpw.mm"
include "wss.mm"
include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "wrex.mm"
include "wral.mm"
include "crab.mm"
include "utopval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "wb.mm"
include "ssid.mm"
include "a1i.mm"
include "wa.mm"
include "cxp.mm"
include "ustssxp.mm"
include "crn.mm"
include "imassrn.mm"
include "rnss.mm"
include "rnxpid.mm"
include "syl6sseq.mm"
include "syl5ss.mm"
include "syl.mm"
include "ralrimiva.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "ustne0.mm"
include "r19.2zb.mm"
include "sylib.mm"
include "mpd.mm"
include "ralrimivw.mm"
include "elutop.mm"
include "mpbir2and.mm"
include "elpwuni.mm"
include "mpbid.mm"
include "eqcomd.mm"

theorem utopbas
  let cU: class U
  let cX: class X
  let va: setvar a
  let vp: setvar p
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y


  assert |- ( U e. ( UnifOn ` X ) -> X = U. ( unifTop ` U ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    cU
    cutop
    cfv
    #
    cuni
    #
    cX
    @0
    @1
    cX
    cpw
    #
    wss
    #
    @2
    cX
    wceq
    #
    @0
    @1
    vv
    cv
    #
    vx
    cv
    csn
    #
    cima
    #
    va
    cv
    #
    wss
    vv
    cU
    wrex
    vx
    @9
    wral
    #
    va
    @3
    crab
    @3
    vx
    vv
    cU
    cX
    va
    utopval
    @10
    va
    @3
    ssrab2
    syl6eqss
    @0
    cX
    @1
    wcel
    #
    @4
    @5
    wb
    @0
    @11
    cX
    cX
    wss
    #
    @8
    cX
    wss
    #
    vv
    cU
    wrex
    #
    vx
    cX
    wral
    @12
    @0
    cX
    ssid
    a1i
    @0
    @14
    vx
    cX
    @0
    @13
    vv
    cU
    wral
    #
    @14
    @0
    @13
    vv
    cU
    @0
    @6
    cU
    wcel
    wa
    @6
    cX
    cX
    cxp
    #
    wss
    #
    @13
    cU
    @6
    cX
    ustssxp
    @17
    @8
    @6
    crn
    #
    cX
    @6
    @7
    imassrn
    @17
    @18
    @16
    crn
    cX
    @6
    @16
    rnss
    cX
    rnxpid
    syl6sseq
    syl5ss
    syl
    ralrimiva
    @0
    cU
    c0
    wne
    @15
    @14
    wi
    cU
    cX
    ustne0
    @13
    vv
    cU
    r19.2zb
    sylib
    mpd
    ralrimivw
    vx
    vv
    cX
    cU
    cX
    elutop
    mpbir2and
    @1
    cX
    elpwuni
    syl
    mpbid
    eqcomd
end
