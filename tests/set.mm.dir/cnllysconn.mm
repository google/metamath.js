include "csconn.mm"
include "clly.mm"
include "wcel.mm"
include "ctop.mm"
include "cv.mm"
include "crest.mm"
include "co.mm"
include "wa.mm"
include "cpw.mm"
include "cin.mm"
include "wrex.mm"
include "wral.mm"
include "cnfldtop.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cbl.mm"
include "cfv.mm"
include "wss.mm"
include "crp.mm"
include "cc.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "cnfldtopn.mm"
include "mopni2.mm"
include "mp3an1.mm"
include "cxr.mm"
include "a1i.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "simpll.mm"
include "toponss.mm"
include "sylancr.mm"
include "simplr.mm"
include "sseldd.mm"
include "rpxr.mm"
include "ad2antrl.mm"
include "blopn.mm"
include "syl3anc.mm"
include "simprr.mm"
include "vex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "elind.mm"
include "simprl.mm"
include "blcntr.mm"
include "eqid.mm"
include "blsconn.mm"
include "syl2anc.mm"
include "wceq.mm"
include "eleq2.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "rgen2.mm"
include "islly.mm"
include "mpbir2an.mm"

theorem cnllysconn
  let cJ: class J
  let vr: setvar r
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume cnllysconn.j: |- J = ( TopOpen ` CCfld )


  assert |- J e. Locally SConn

  proof
    cJ
    csconn
    clly
    wcel
    cJ
    ctop
    wcel
    vy
    cv
    #
    vu
    cv
    #
    wcel
    #
    cJ
    @1
    crest
    co
    #
    csconn
    wcel
    #
    wa
    #
    vu
    cJ
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
    @6
    wral
    vx
    cJ
    wral
    cJ
    cnllysconn.j
    cnfldtop
    @9
    vx
    vy
    cJ
    @6
    @6
    cJ
    wcel
    #
    @0
    @6
    wcel
    #
    wa
    #
    @0
    vr
    cv
    #
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    co
    #
    @6
    wss
    #
    @9
    vr
    crp
    @14
    cc
    cxmt
    cfv
    wcel
    #
    @10
    @11
    @16
    vr
    crp
    wrex
    cnxmet
    vr
    @6
    @14
    @0
    cJ
    cc
    cJ
    cnllysconn.j
    cnfldtopn
    #
    mopni2
    mp3an1
    @12
    @13
    crp
    wcel
    #
    @16
    wa
    #
    wa
    #
    @15
    @8
    wcel
    @0
    @15
    wcel
    #
    cJ
    @15
    crest
    co
    #
    csconn
    wcel
    #
    @9
    @21
    cJ
    @7
    @15
    @21
    @17
    @0
    cc
    wcel
    #
    @13
    cxr
    wcel
    #
    @15
    cJ
    wcel
    @17
    @21
    cnxmet
    a1i
    #
    @21
    @6
    cc
    @0
    @21
    cJ
    cc
    ctopon
    cfv
    wcel
    @10
    @6
    cc
    wss
    cJ
    cnllysconn.j
    cnfldtopon
    @10
    @11
    @20
    simpll
    @6
    cJ
    cc
    toponss
    sylancr
    @10
    @11
    @20
    simplr
    sseldd
    #
    @19
    @26
    @12
    @16
    @13
    rpxr
    ad2antrl
    #
    @14
    @0
    @13
    cJ
    cc
    @18
    blopn
    syl3anc
    @21
    @16
    @15
    @7
    wcel
    @12
    @19
    @16
    simprr
    @15
    @6
    vx
    vex
    elpw2
    sylibr
    elind
    @21
    @17
    @25
    @19
    @22
    @27
    @28
    @12
    @19
    @16
    simprl
    @14
    @0
    @13
    cc
    blcntr
    syl3anc
    @21
    @25
    @26
    @24
    @28
    @29
    @0
    @13
    @15
    cJ
    @23
    cnllysconn.j
    @15
    eqid
    @23
    eqid
    blsconn
    syl2anc
    @5
    @22
    @24
    wa
    vu
    @15
    @8
    @1
    @15
    wceq
    #
    @2
    @22
    @4
    @24
    @1
    @15
    @0
    eleq2
    @30
    @3
    @23
    csconn
    @1
    @15
    cJ
    crest
    oveq2
    eleq1d
    anbi12d
    rspcev
    syl12anc
    rexlimddv
    rgen2
    vx
    vy
    vu
    csconn
    cJ
    islly
    mpbir2an
end
