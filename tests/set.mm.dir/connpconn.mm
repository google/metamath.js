include "cconn.mm"
include "wcel.mm"
include "cpconn.mm"
include "cnlly.mm"
include "wa.mm"
include "ctop.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "wrex.mm"
include "cuni.mm"
include "wral.mm"
include "conntop.mm"
include "adantr.mm"
include "crab.mm"
include "eqid.mm"
include "simpll.mm"
include "ccld.mm"
include "cin.mm"
include "inss1.mm"
include "wel.mm"
include "wss.mm"
include "wi.mm"
include "crest.mm"
include "w3a.mm"
include "cpw.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "topopn.mm"
include "syl.mm"
include "simprr.mm"
include "nlly2i.mm"
include "syl3anc.mm"
include "simprr1.mm"
include "weq.mm"
include "eqeq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "elrab.mm"
include "simprbi.mm"
include "simprr3.mm"
include "simprr2.mm"
include "simprll.mm"
include "sseldd.mm"
include "elpwi.mm"
include "ad2antrl.mm"
include "restuni.mm"
include "syl2anc.mm"
include "eleqtrd.mm"
include "pconncn.mm"
include "cpco.mm"
include "simplrl.mm"
include "ad2antlr.mm"
include "cnrest2r.mm"
include "simprl.mm"
include "simplrr.mm"
include "simprd.mm"
include "simprrl.mm"
include "eqtr4d.mm"
include "pcocn.mm"
include "pco0.mm"
include "simpld.mm"
include "eqtrd.mm"
include "pco1.mm"
include "simprrr.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "rexlimddv.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "rexlimdvaa.mm"
include "sstrd.mm"
include "jctild.mm"
include "cbvrexv.mm"
include "ssrab.mm"
include "3imtr4g.mm"
include "syl5.mm"
include "jca.mm"
include "expr.mm"
include "reximdv.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "wb.mm"
include "ssrab2.mm"
include "isclo2.mm"
include "sylancl.mm"
include "mpbird.mm"
include "sseldi.mm"
include "c0.mm"
include "wne.mm"
include "cicc.mm"
include "csn.mm"
include "cxp.mm"
include "simpr.mm"
include "ctopon.mm"
include "iitopon.mm"
include "a1i.mm"
include "toptopon.mm"
include "sylib.mm"
include "cnconst2.mm"
include "0elunit.mm"
include "vex.mm"
include "fvconst2.mm"
include "mp1i.mm"
include "1elunit.mm"
include "rspc2ev.mm"
include "syl112anc.mm"
include "rabn0.mm"
include "sylibr.mm"
include "inss2.mm"
include "connclo.mm"
include "eqcomd.mm"
include "rabid2.mm"
include "ispconn.mm"
include "sylanbrc.mm"

theorem connpconn
  let cJ: class J
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vg: setvar g
  let vh: setvar h
  let vs: setvar s
  let vu: setvar u
  let vw: setvar w


  assert |- ( ( J e. Conn /\ J e. N-Locally PConn ) -> J e. PConn )

  proof
    cJ
    cconn
    wcel
    #
    cJ
    cpconn
    cnlly
    wcel
    #
    wa
    #
    cJ
    ctop
    wcel
    #
    cc0
    vf
    cv
    #
    cfv
    #
    vx
    cv
    #
    wceq
    #
    c1
    @4
    cfv
    #
    vy
    cv
    #
    wceq
    #
    wa
    #
    vf
    cii
    cJ
    ccn
    co
    #
    wrex
    #
    vy
    cJ
    cuni
    #
    wral
    #
    vx
    @14
    wral
    cJ
    cpconn
    wcel
    @0
    @3
    @1
    cJ
    conntop
    #
    adantr
    @2
    @15
    vx
    @14
    @2
    @6
    @14
    wcel
    #
    wa
    #
    @14
    @13
    vy
    @14
    crab
    #
    wceq
    @15
    @18
    @19
    @14
    @18
    @19
    cJ
    @14
    @14
    eqid
    #
    @0
    @1
    @17
    simpll
    @18
    cJ
    cJ
    ccld
    cfv
    #
    cin
    #
    cJ
    @19
    cJ
    @21
    inss1
    @18
    @19
    @22
    wcel
    #
    vz
    vu
    wel
    #
    vw
    cv
    #
    @19
    wcel
    #
    vu
    cv
    #
    @19
    wss
    #
    wi
    #
    vw
    @27
    wral
    #
    wa
    #
    vu
    cJ
    wrex
    #
    vz
    @14
    wral
    #
    @18
    @32
    vz
    @14
    @2
    @17
    vz
    cv
    #
    @14
    wcel
    #
    @32
    @2
    @17
    @35
    wa
    #
    wa
    #
    @24
    @27
    vs
    cv
    #
    wss
    #
    cJ
    @38
    crest
    co
    #
    cpconn
    wcel
    #
    w3a
    #
    vu
    cJ
    wrex
    #
    vs
    @14
    cpw
    #
    wrex
    #
    @32
    @37
    @1
    @14
    cJ
    wcel
    #
    @35
    @45
    @0
    @1
    @36
    simplr
    @37
    @3
    @46
    @0
    @3
    @1
    @36
    @16
    ad2antrr
    #
    cJ
    @14
    @20
    topopn
    syl
    @2
    @17
    @35
    simprr
    vu
    cpconn
    @34
    @14
    cJ
    vs
    nlly2i
    syl3anc
    @37
    @43
    @32
    vs
    @44
    @37
    @38
    @44
    wcel
    #
    wa
    @42
    @31
    vu
    cJ
    @37
    @48
    @42
    @31
    @37
    @48
    @42
    wa
    #
    wa
    #
    @24
    @30
    @24
    @39
    @41
    @48
    @37
    simprr1
    @50
    @29
    vw
    @27
    @26
    @7
    @8
    @25
    wceq
    #
    wa
    #
    vf
    @12
    wrex
    #
    @50
    vw
    vu
    wel
    #
    wa
    #
    @28
    @26
    @25
    @14
    wcel
    @53
    @13
    @53
    vy
    @25
    @14
    vy
    vw
    weq
    #
    @11
    @52
    vf
    @12
    @56
    @10
    @51
    @7
    @9
    @25
    @8
    eqeq2
    anbi2d
    rexbidv
    elrab
    simprbi
    @55
    cc0
    vg
    cv
    #
    cfv
    #
    @6
    wceq
    #
    c1
    @57
    cfv
    #
    @25
    wceq
    #
    wa
    #
    vg
    @12
    wrex
    #
    @27
    @14
    wss
    #
    @13
    vy
    @27
    wral
    #
    wa
    @53
    @28
    @55
    @63
    @65
    @64
    @55
    @62
    @65
    vg
    @12
    @50
    @54
    @57
    @12
    wcel
    #
    @62
    wa
    #
    @65
    @50
    @54
    @67
    wa
    #
    wa
    @13
    vy
    @27
    @50
    @68
    vy
    vu
    wel
    #
    @13
    @50
    @68
    @69
    wa
    #
    wa
    #
    cc0
    vh
    cv
    #
    cfv
    #
    @25
    wceq
    #
    c1
    @72
    cfv
    #
    @9
    wceq
    #
    wa
    #
    @13
    vh
    cii
    @40
    ccn
    co
    #
    @71
    @41
    @25
    @40
    cuni
    #
    wcel
    @9
    @79
    wcel
    @77
    vh
    @78
    wrex
    @50
    @41
    @70
    @24
    @39
    @41
    @48
    @37
    simprr3
    adantr
    @71
    @25
    @38
    @79
    @71
    @27
    @38
    @25
    @50
    @39
    @70
    @24
    @39
    @41
    @48
    @37
    simprr2
    #
    adantr
    #
    @50
    @54
    @67
    @69
    simprll
    sseldd
    @71
    @3
    @38
    @14
    wss
    #
    @38
    @79
    wceq
    @37
    @3
    @49
    @70
    @47
    ad2antrr
    #
    @50
    @82
    @70
    @48
    @82
    @37
    @42
    @38
    @14
    elpwi
    #
    ad2antrl
    adantr
    @38
    cJ
    @14
    @20
    restuni
    syl2anc
    #
    eleqtrd
    @71
    @9
    @38
    @79
    @71
    @27
    @38
    @9
    @81
    @50
    @68
    @69
    simprr
    sseldd
    @85
    eleqtrd
    @25
    @9
    vh
    @40
    @79
    @79
    eqid
    pconncn
    syl3anc
    @71
    @72
    @78
    wcel
    #
    @77
    wa
    #
    wa
    #
    @57
    @72
    cJ
    cpco
    cfv
    co
    #
    @12
    wcel
    cc0
    @89
    cfv
    #
    @6
    wceq
    #
    c1
    @89
    cfv
    #
    @9
    wceq
    #
    @13
    @88
    @57
    @72
    cJ
    @70
    @66
    @50
    @87
    @54
    @66
    @62
    @69
    simplrl
    ad2antlr
    #
    @88
    @78
    @12
    @72
    @88
    @3
    @78
    @12
    wss
    @71
    @3
    @87
    @83
    adantr
    @38
    cii
    cJ
    cnrest2r
    syl
    @71
    @86
    @77
    simprl
    sseldd
    #
    @88
    @60
    @25
    @73
    @88
    @59
    @61
    @70
    @62
    @50
    @87
    @54
    @66
    @62
    @69
    simplrr
    ad2antlr
    #
    simprd
    @71
    @86
    @74
    @76
    simprrl
    eqtr4d
    pcocn
    @88
    @90
    @58
    @6
    @88
    @57
    @72
    cJ
    @94
    @95
    pco0
    @88
    @59
    @61
    @96
    simpld
    eqtrd
    @88
    @92
    @75
    @9
    @88
    @57
    @72
    cJ
    @94
    @95
    pco1
    @71
    @86
    @74
    @76
    simprrr
    eqtrd
    @11
    @91
    @93
    wa
    vf
    @89
    @12
    @4
    @89
    wceq
    #
    @7
    @91
    @10
    @93
    @97
    @5
    @90
    @6
    cc0
    @4
    @89
    fveq1
    eqeq1d
    @97
    @8
    @92
    @9
    c1
    @4
    @89
    fveq1
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    rexlimddv
    anassrs
    ralrimiva
    anassrs
    rexlimdvaa
    @55
    @27
    @38
    @14
    @50
    @39
    @54
    @80
    adantr
    @55
    @48
    @82
    @37
    @48
    @42
    @54
    simplrl
    @84
    syl
    sstrd
    jctild
    @52
    @62
    vf
    vg
    @12
    vf
    vg
    weq
    #
    @7
    @59
    @51
    @61
    @98
    @5
    @58
    @6
    cc0
    @4
    @57
    fveq1
    eqeq1d
    @98
    @8
    @60
    @25
    c1
    @4
    @57
    fveq1
    eqeq1d
    anbi12d
    cbvrexv
    @13
    vy
    @14
    @27
    ssrab
    3imtr4g
    syl5
    ralrimiva
    jca
    expr
    reximdv
    rexlimdva
    mpd
    anassrs
    ralrimiva
    @18
    @3
    @19
    @14
    wss
    @23
    @33
    wb
    @0
    @3
    @1
    @17
    @16
    ad2antrr
    #
    @13
    vy
    @14
    ssrab2
    vz
    vu
    vw
    @19
    cJ
    @14
    @20
    isclo2
    sylancl
    mpbird
    #
    sseldi
    @18
    @13
    vy
    @14
    wrex
    #
    @19
    c0
    wne
    @18
    @17
    cc0
    c1
    cicc
    co
    #
    @6
    csn
    cxp
    #
    @12
    wcel
    #
    cc0
    @103
    cfv
    #
    @6
    wceq
    #
    c1
    @103
    cfv
    #
    @6
    wceq
    #
    @101
    @2
    @17
    simpr
    #
    @18
    cii
    @102
    ctopon
    cfv
    wcel
    #
    cJ
    @14
    ctopon
    cfv
    wcel
    #
    @17
    @104
    @110
    @18
    iitopon
    a1i
    @18
    @3
    @111
    @99
    cJ
    @14
    @20
    toptopon
    sylib
    @109
    @6
    cii
    cJ
    @102
    @14
    cnconst2
    syl3anc
    cc0
    @102
    wcel
    @106
    @18
    0elunit
    @102
    @6
    cc0
    vx
    vex
    #
    fvconst2
    mp1i
    c1
    @102
    wcel
    @108
    @18
    1elunit
    @102
    @6
    c1
    @112
    fvconst2
    mp1i
    @11
    @106
    @108
    wa
    @7
    @8
    @6
    wceq
    #
    wa
    vy
    vf
    @6
    @103
    @14
    @12
    vy
    vx
    weq
    @10
    @113
    @7
    @9
    @6
    @8
    eqeq2
    anbi2d
    @4
    @103
    wceq
    #
    @7
    @106
    @113
    @108
    @114
    @5
    @105
    @6
    cc0
    @4
    @103
    fveq1
    eqeq1d
    @114
    @8
    @107
    @6
    c1
    @4
    @103
    fveq1
    eqeq1d
    anbi12d
    rspc2ev
    syl112anc
    @13
    vy
    @14
    rabn0
    sylibr
    @18
    @22
    @21
    @19
    cJ
    @21
    inss2
    @100
    sseldi
    connclo
    eqcomd
    @13
    vy
    @14
    rabid2
    sylib
    ralrimiva
    vx
    vy
    vf
    cJ
    @14
    @20
    ispconn
    sylanbrc
end
