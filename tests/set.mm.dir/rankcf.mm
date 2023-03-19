include "crnk.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "csuc.mm"
include "con0.mm"
include "wrex.mm"
include "cvv.mm"
include "wcel.mm"
include "wlim.mm"
include "wa.mm"
include "w3o.mm"
include "ccf.mm"
include "csdm.mm"
include "wbr.mm"
include "wn.mm"
include "rankon.mm"
include "onzsl.mm"
include "mpbi.mm"
include "sdom0.mm"
include "fveq2.mm"
include "cf0.mm"
include "syl6eq.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "cdom.mm"
include "c1o.mm"
include "cfsuc.mm"
include "sylan9eqr.mm"
include "wne.mm"
include "nsuceq0.mm"
include "neeq1.mm"
include "mpbiri.mm"
include "cr1.mm"
include "cdm.mm"
include "0elon.mm"
include "wfn.mm"
include "r1fnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleqtrri.mm"
include "rankonid.mm"
include "necon3i.mm"
include "cima.mm"
include "cuni.mm"
include "wb.mm"
include "rankvaln.mm"
include "necon1ai.mm"
include "breq2.mm"
include "0sdom1dom.mm"
include "vex.mm"
include "0sdom.mm"
include "bitr3i.mm"
include "vtoclbg.mm"
include "syl.mm"
include "mpbird.mm"
include "adantl.mm"
include "eqbrtrd.mm"
include "rexlimiva.mm"
include "domnsym.mm"
include "csn.mm"
include "cab.mm"
include "wss.mm"
include "wi.mm"
include "nlim0.mm"
include "limeq.mm"
include "con4i.mm"
include "r1elssi.mm"
include "sselda.mm"
include "ranksnb.mm"
include "rankelb.mm"
include "limsuc.mm"
include "sylibd.mm"
include "imp.mm"
include "eqeltrd.mm"
include "eleq1a.mm"
include "rexlimdva.mm"
include "abssdv.mm"
include "ciun.mm"
include "snex.mm"
include "dfiun2.mm"
include "iunid.mm"
include "eqtr3i.mm"
include "fveq2i.mm"
include "snwf.mm"
include "3syl.mm"
include "abrexexg.mm"
include "eleq1.mm"
include "sseq1.mm"
include "r1elss.mm"
include "rankuni2b.mm"
include "syl5eqr.mm"
include "fvex.mm"
include "abrexco.mm"
include "unieqi.mm"
include "eqtri.mm"
include "syl6req.mm"
include "cfslb.mm"
include "mpd3an23.mm"
include "fveq2d.mm"
include "breq12.mm"
include "mpdan.mm"
include "rexeq.mm"
include "abbidv.mm"
include "mpancom.mm"
include "imbi12d.mm"
include "cmpt.mm"
include "crn.mm"
include "eqid.mm"
include "rnmpt.mm"
include "ccrd.mm"
include "wfo.mm"
include "cfon.mm"
include "sdomdom.mm"
include "ondomen.mm"
include "sylancr.mm"
include "fnmpti.mm"
include "dffn4.mm"
include "fodomnum.mm"
include "mpisyl.mm"
include "syl5eqbrr.mm"
include "vtoclg.mm"
include "domtr.mm"
include "syl6an.mm"
include "pm2.01d.mm"
include "3jaoi.mm"

theorem rankcf
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- -. A ~< ( cf ` ( rank ` A ) )

  proof
    cA
    crnk
    cfv
    #
    c0
    wceq
    #
    @0
    vx
    cv
    #
    csuc
    #
    wceq
    #
    vx
    con0
    wrex
    #
    @0
    cvv
    wcel
    #
    @0
    wlim
    #
    wa
    #
    w3o
    #
    cA
    @0
    ccf
    cfv
    #
    csdm
    wbr
    #
    wn
    #
    @0
    con0
    wcel
    @9
    cA
    rankon
    vx
    @0
    onzsl
    mpbi
    @1
    @12
    @5
    @8
    @1
    @11
    cA
    c0
    csdm
    wbr
    cA
    sdom0
    @1
    @10
    c0
    cA
    csdm
    @1
    @10
    c0
    ccf
    cfv
    c0
    @0
    c0
    ccf
    fveq2
    cf0
    syl6eq
    breq2d
    mtbiri
    @5
    @10
    cA
    cdom
    wbr
    #
    @12
    @4
    @13
    vx
    con0
    @2
    con0
    wcel
    #
    @4
    wa
    @10
    c1o
    cA
    cdom
    @4
    @14
    @10
    @3
    ccf
    cfv
    c1o
    @0
    @3
    ccf
    fveq2
    @2
    cfsuc
    sylan9eqr
    @4
    c1o
    cA
    cdom
    wbr
    #
    @14
    @4
    @0
    c0
    wne
    #
    @15
    @4
    @16
    @3
    c0
    wne
    @2
    nsuceq0
    @0
    @3
    c0
    neeq1
    mpbiri
    @16
    @15
    cA
    c0
    wne
    #
    cA
    c0
    @0
    c0
    cA
    c0
    wceq
    @0
    c0
    crnk
    cfv
    #
    c0
    cA
    c0
    crnk
    fveq2
    c0
    cr1
    cdm
    #
    wcel
    @18
    c0
    wceq
    c0
    con0
    @19
    0elon
    cr1
    con0
    wfn
    @19
    con0
    wceq
    r1fnon
    con0
    cr1
    fndm
    ax-mp
    eleqtrri
    c0
    rankonid
    mpbi
    syl6eq
    necon3i
    @16
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    @15
    @17
    wb
    @21
    @0
    c0
    cA
    rankvaln
    #
    necon1ai
    c1o
    vy
    cv
    #
    cdom
    wbr
    #
    @23
    c0
    wne
    #
    @15
    @17
    vy
    cA
    @20
    @23
    cA
    c1o
    cdom
    breq2
    @23
    cA
    c0
    neeq1
    @24
    c0
    @23
    csdm
    wbr
    @25
    @23
    0sdom1dom
    @23
    vy
    vex
    0sdom
    bitr3i
    vtoclbg
    syl
    mpbird
    syl
    adantl
    eqbrtrd
    rexlimiva
    @10
    cA
    domnsym
    #
    syl
    @7
    @12
    @6
    @7
    @11
    @7
    @10
    vw
    cv
    #
    @2
    csn
    #
    crnk
    cfv
    #
    wceq
    #
    vx
    cA
    wrex
    #
    vw
    cab
    #
    cdom
    wbr
    #
    @11
    @32
    cA
    cdom
    wbr
    #
    @12
    @7
    @32
    @0
    wss
    @32
    cuni
    #
    @0
    wceq
    #
    @33
    @7
    @31
    vw
    @0
    @7
    @30
    @27
    @0
    wcel
    #
    vx
    cA
    @7
    @2
    cA
    wcel
    #
    wa
    #
    @29
    @0
    wcel
    @30
    @37
    wi
    @39
    @29
    @2
    crnk
    cfv
    #
    csuc
    #
    @0
    @39
    @2
    @20
    wcel
    #
    @29
    @41
    wceq
    @7
    cA
    @20
    @2
    @7
    @21
    cA
    @20
    wss
    @21
    @7
    @21
    wn
    @1
    @7
    wn
    @22
    @1
    @7
    c0
    wlim
    nlim0
    @0
    c0
    limeq
    mtbiri
    syl
    con4i
    #
    cA
    r1elssi
    #
    syl
    sselda
    @2
    ranksnb
    syl
    @7
    @38
    @41
    @0
    wcel
    #
    @7
    @38
    @40
    @0
    wcel
    #
    @45
    @7
    @21
    @38
    @46
    wi
    @43
    @2
    cA
    rankelb
    syl
    @0
    @40
    limsuc
    sylibd
    imp
    eqeltrd
    @29
    @0
    @27
    eleq1a
    syl
    rexlimdva
    abssdv
    @7
    @21
    @36
    @43
    @21
    @0
    vz
    @23
    @28
    wceq
    #
    vx
    cA
    wrex
    #
    vy
    cab
    #
    vz
    cv
    #
    crnk
    cfv
    #
    ciun
    #
    @35
    @21
    @0
    @49
    cuni
    #
    crnk
    cfv
    #
    @52
    @53
    cA
    crnk
    vx
    cA
    @28
    ciun
    @53
    cA
    vx
    vy
    cA
    @28
    @2
    snex
    #
    dfiun2
    vx
    cA
    iunid
    eqtr3i
    fveq2i
    @21
    @49
    @20
    wcel
    #
    @54
    @52
    wceq
    @21
    @56
    @49
    @20
    wss
    #
    @21
    @48
    vy
    @20
    @21
    @47
    @23
    @20
    wcel
    #
    vx
    cA
    @21
    @38
    wa
    @42
    @28
    @20
    wcel
    @47
    @58
    wi
    @21
    cA
    @20
    @2
    @44
    sselda
    @2
    snwf
    @28
    @20
    @23
    eleq1a
    3syl
    rexlimdva
    abssdv
    @21
    @49
    cvv
    wcel
    @56
    @57
    wb
    vx
    vy
    cA
    @28
    @20
    abrexexg
    @50
    @20
    wcel
    @50
    @20
    wss
    @56
    @57
    vz
    @49
    cvv
    @50
    @49
    @20
    eleq1
    @50
    @49
    @20
    sseq1
    @50
    vz
    vex
    r1elss
    vtoclbg
    syl
    mpbird
    vz
    @49
    rankuni2b
    syl
    syl5eqr
    @52
    @27
    @51
    wceq
    vz
    @49
    wrex
    vw
    cab
    #
    cuni
    @35
    vz
    vw
    @49
    @51
    @50
    crnk
    fvex
    dfiun2
    @59
    @32
    vw
    vz
    vy
    vx
    cA
    @28
    @51
    @29
    @55
    @50
    @28
    crnk
    fveq2
    abrexco
    unieqi
    eqtri
    syl6req
    syl
    @0
    @32
    cA
    crnk
    fvex
    cfslb
    mpd3an23
    @7
    @21
    @11
    @34
    wi
    #
    @43
    @23
    @23
    crnk
    cfv
    #
    ccf
    cfv
    #
    csdm
    wbr
    #
    @30
    vx
    @23
    wrex
    #
    vw
    cab
    #
    @23
    cdom
    wbr
    #
    wi
    @60
    vy
    cA
    @20
    @23
    cA
    wceq
    #
    @63
    @11
    @66
    @34
    @67
    @62
    @10
    wceq
    @63
    @11
    wb
    @67
    @61
    @0
    ccf
    @23
    cA
    crnk
    fveq2
    fveq2d
    @23
    cA
    @62
    @10
    csdm
    breq12
    mpdan
    @65
    @32
    wceq
    @67
    @66
    @34
    wb
    @67
    @64
    @31
    vw
    @30
    vx
    @23
    cA
    rexeq
    abbidv
    @65
    @32
    @23
    cA
    cdom
    breq12
    mpancom
    imbi12d
    @63
    @65
    vx
    @23
    @29
    cmpt
    #
    crn
    #
    @23
    cdom
    vx
    vw
    @23
    @29
    @68
    @68
    eqid
    #
    rnmpt
    @63
    @23
    ccrd
    cdm
    wcel
    #
    @23
    @69
    @68
    wfo
    #
    @69
    @23
    cdom
    wbr
    @63
    @62
    con0
    wcel
    @23
    @62
    cdom
    wbr
    @71
    @61
    cfon
    @23
    @62
    sdomdom
    @62
    @23
    ondomen
    sylancr
    @68
    @23
    wfn
    @72
    vx
    @23
    @29
    @68
    @28
    crnk
    fvex
    @70
    fnmpti
    @23
    @68
    dffn4
    mpbi
    @23
    @69
    @68
    fodomnum
    mpisyl
    syl5eqbrr
    vtoclg
    syl
    @33
    @34
    wa
    @13
    @12
    @10
    @32
    cA
    domtr
    @26
    syl
    syl6an
    pm2.01d
    adantl
    3jaoi
    ax-mp
end
