include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "csconn.mm"
include "clly.mm"
include "wcel.mm"
include "ctop.mm"
include "wel.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "wa.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "retop.mm"
include "wss.mm"
include "tg2.mm"
include "ctb.mm"
include "retopbas.mm"
include "bastg.mm"
include "ax-mp.mm"
include "simprl.mm"
include "sseldi.mm"
include "simprrr.mm"
include "selpw.mm"
include "sylibr.mm"
include "elind.mm"
include "simprrl.mm"
include "wceq.mm"
include "cxr.mm"
include "cxp.mm"
include "cr.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "ioof.mm"
include "ffn.mm"
include "ovelrn.mm"
include "mp2b.mm"
include "oveq2.mm"
include "ioosconn.mm"
include "syl6eqel.mm"
include "rexlimivw.mm"
include "sylbi.mm"
include "ad2antrl.mm"
include "jca32.mm"
include "ex.mm"
include "reximdv2.mm"
include "mpd.mm"
include "rgen2.mm"
include "islly.mm"
include "mpbir2an.mm"

theorem rellysconn
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B


  assert |- ( topGen ` ran (,) ) e. Locally SConn

  proof
    cioo
    crn
    #
    ctg
    cfv
    #
    csconn
    clly
    wcel
    @1
    ctop
    wcel
    vy
    vz
    wel
    #
    @1
    vz
    cv
    #
    crest
    co
    #
    csconn
    wcel
    #
    wa
    #
    vz
    @1
    vx
    cv
    #
    cpw
    #
    cin
    #
    wrex
    #
    vy
    @7
    wral
    vx
    @1
    wral
    retop
    @10
    vx
    vy
    @1
    @7
    @7
    @1
    wcel
    vy
    vx
    wel
    wa
    #
    @2
    @3
    @7
    wss
    #
    wa
    #
    vz
    @0
    wrex
    @10
    vz
    @7
    @0
    vy
    cv
    tg2
    @11
    @13
    @6
    vz
    @0
    @9
    @11
    @3
    @0
    wcel
    #
    @13
    wa
    #
    @3
    @9
    wcel
    #
    @6
    wa
    @11
    @15
    wa
    #
    @16
    @2
    @5
    @17
    @1
    @8
    @3
    @17
    @0
    @1
    @3
    @0
    ctb
    wcel
    @0
    @1
    wss
    retopbas
    @0
    ctb
    bastg
    ax-mp
    @11
    @14
    @13
    simprl
    sseldi
    @17
    @12
    @3
    @8
    wcel
    @11
    @14
    @2
    @12
    simprrr
    vz
    @7
    selpw
    sylibr
    elind
    @11
    @14
    @2
    @12
    simprrl
    @14
    @5
    @11
    @13
    @14
    @3
    va
    cv
    #
    vb
    cv
    #
    cioo
    co
    #
    wceq
    #
    vb
    cxr
    wrex
    #
    va
    cxr
    wrex
    #
    @5
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    cioo
    @24
    wfn
    @14
    @23
    wb
    ioof
    @24
    @25
    cioo
    ffn
    va
    vb
    cxr
    cxr
    @3
    cioo
    ovelrn
    mp2b
    @22
    @5
    va
    cxr
    @21
    @5
    vb
    cxr
    @21
    @4
    @1
    @20
    crest
    co
    csconn
    @3
    @20
    @1
    crest
    oveq2
    @18
    @19
    ioosconn
    syl6eqel
    rexlimivw
    rexlimivw
    sylbi
    ad2antrl
    jca32
    ex
    reximdv2
    mpd
    rgen2
    vx
    vy
    vz
    csconn
    @1
    islly
    mpbir2an
end
