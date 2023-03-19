include "cgch.mm"
include "cvv.mm"
include "wceq.mm"
include "cwina.mm"
include "cina.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "c0.mm"
include "wne.mm"
include "ccf.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "cpw.mm"
include "idd.mm"
include "cfn.mm"
include "wi.mm"
include "pwfi.mm"
include "com.mm"
include "isfinite.mm"
include "cdom.mm"
include "wss.mm"
include "winainf.mm"
include "ssdomg.mm"
include "mpd.mm"
include "sdomdomtr.mm"
include "expcom.mm"
include "syl.mm"
include "syl5bi.mm"
include "ad3antlr.mm"
include "a1dd.mm"
include "wn.mm"
include "wb.mm"
include "vex.mm"
include "simplll.mm"
include "syl5eleqr.mm"
include "simprr.mm"
include "gchinf.mm"
include "syl2anc.mm"
include "gchpwdom.mm"
include "syl3anc.mm"
include "ccrd.mm"
include "winacard.mm"
include "con0.mm"
include "iscard.mm"
include "simprbi.mm"
include "ad2antlr.mm"
include "r19.21bi.mm"
include "domsdomtr.mm"
include "adantrr.mm"
include "sylbid.mm"
include "expr.mm"
include "pm2.61d.mm"
include "rexlimdva.mm"
include "ralimdva.mm"
include "3anim123d.mm"
include "elwina.mm"
include "elina.mm"
include "3imtr4g.mm"
include "ex.mm"
include "inawina.mm"
include "impbid1.mm"
include "eqrdv.mm"

theorem gchina
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( GCH = _V -> InaccW = Inacc )

  proof
    cgch
    cvv
    wceq
    #
    vx
    cwina
    cina
    @0
    vx
    cv
    #
    cwina
    wcel
    #
    @1
    cina
    wcel
    #
    @0
    @2
    @3
    @0
    @2
    wa
    #
    @2
    @3
    @0
    @2
    simpr
    @4
    @1
    c0
    wne
    #
    @1
    ccf
    cfv
    @1
    wceq
    #
    vy
    cv
    #
    vz
    cv
    #
    csdm
    wbr
    #
    vz
    @1
    wrex
    #
    vy
    @1
    wral
    #
    w3a
    @5
    @6
    @7
    cpw
    #
    @1
    csdm
    wbr
    #
    vy
    @1
    wral
    #
    w3a
    @2
    @3
    @4
    @5
    @5
    @6
    @6
    @11
    @14
    @4
    @5
    idd
    @4
    @6
    idd
    @4
    @10
    @13
    vy
    @1
    @4
    @7
    @1
    wcel
    #
    wa
    #
    @9
    @13
    vz
    @1
    @16
    @8
    @1
    wcel
    #
    wa
    #
    @7
    cfn
    wcel
    #
    @9
    @13
    wi
    #
    @18
    @19
    @13
    @9
    @2
    @19
    @13
    wi
    @0
    @15
    @17
    @19
    @12
    cfn
    wcel
    #
    @2
    @13
    @7
    pwfi
    @21
    @12
    com
    csdm
    wbr
    #
    @2
    @13
    @12
    isfinite
    @2
    com
    @1
    cdom
    wbr
    #
    @22
    @13
    wi
    @2
    com
    @1
    wss
    @23
    @1
    winainf
    com
    @1
    cwina
    ssdomg
    mpd
    @22
    @23
    @13
    @12
    com
    @1
    sdomdomtr
    expcom
    syl
    syl5bi
    syl5bi
    ad3antlr
    a1dd
    @16
    @17
    @19
    wn
    #
    @20
    @16
    @17
    @24
    wa
    #
    wa
    #
    @9
    @12
    @8
    cdom
    wbr
    #
    @13
    @26
    com
    @7
    cdom
    wbr
    #
    @7
    cgch
    wcel
    #
    @8
    cgch
    wcel
    @9
    @27
    wb
    @26
    @29
    @24
    @28
    @26
    @7
    cvv
    cgch
    vy
    vex
    @0
    @2
    @15
    @25
    simplll
    #
    syl5eleqr
    #
    @16
    @17
    @24
    simprr
    @7
    gchinf
    syl2anc
    @31
    @26
    @8
    cvv
    cgch
    vz
    vex
    @30
    syl5eleqr
    @7
    @8
    gchpwdom
    syl3anc
    @16
    @17
    @27
    @13
    wi
    #
    @24
    @18
    @8
    @1
    csdm
    wbr
    #
    @32
    @16
    @33
    vz
    @1
    @2
    @33
    vz
    @1
    wral
    #
    @0
    @15
    @2
    @1
    ccrd
    cfv
    @1
    wceq
    #
    @34
    @1
    winacard
    @35
    @1
    con0
    wcel
    @34
    vz
    @1
    iscard
    simprbi
    syl
    ad2antlr
    r19.21bi
    @27
    @33
    @13
    @12
    @8
    @1
    domsdomtr
    expcom
    syl
    adantrr
    sylbid
    expr
    pm2.61d
    rexlimdva
    ralimdva
    3anim123d
    vy
    vz
    @1
    elwina
    vy
    @1
    elina
    3imtr4g
    mpd
    ex
    @1
    inawina
    impbid1
    eqrdv
end
