include "ctop.mm"
include "wcel.mm"
include "cha.mm"
include "wa.mm"
include "cxko.mm"
include "co.mm"
include "cv.mm"
include "wne.mm"
include "wel.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "wrex.mm"
include "wi.mm"
include "cuni.mm"
include "wral.mm"
include "haustop.mm"
include "xkotop.mm"
include "sylan2.mm"
include "ccn.mm"
include "eqid.mm"
include "xkouni.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "cfv.mm"
include "wn.mm"
include "wfn.mm"
include "weq.mm"
include "wb.mm"
include "wf.mm"
include "simprl.mm"
include "cnf.mm"
include "syl.mm"
include "ffn.mm"
include "simprr.mm"
include "eqfnfv.mm"
include "syl2anc.mm"
include "necon3abid.mm"
include "rexnal.mm"
include "df-ne.mm"
include "simpllr.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "hausnei.mm"
include "syl13anc.mm"
include "expr.mm"
include "syl5bir.mm"
include "csn.mm"
include "cima.mm"
include "wss.mm"
include "crab.mm"
include "simp-4l.mm"
include "ad4antlr.mm"
include "simplr.mm"
include "snssd.mm"
include "crest.mm"
include "cpw.mm"
include "ccmp.mm"
include "ctopon.mm"
include "toptopon.mm"
include "sylib.mm"
include "restsn2.mm"
include "cfn.mm"
include "snfi.mm"
include "discmp.mm"
include "mpbi.mm"
include "syl6eqel.mm"
include "simprll.mm"
include "xkoopn.mm"
include "simprlr.mm"
include "ad2antrr.mm"
include "fnsnfv.mm"
include "simprr1.mm"
include "eqsstr3d.mm"
include "imaeq1.mm"
include "sseq1d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "simprr2.mm"
include "inrab.mm"
include "cdm.mm"
include "fdm.mm"
include "adantl.mm"
include "eleqtrrd.mm"
include "simprr3.mm"
include "sseq0.mm"
include "expcom.mm"
include "imadisj.mm"
include "disjsn.mm"
include "bitri.mm"
include "syl6ib.mm"
include "mt2d.mm"
include "ssin.mm"
include "sylnibr.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "syl5eq.mm"
include "eleq2.mm"
include "ineq1.mm"
include "eqeq1d.mm"
include "3anbi13d.mm"
include "ineq2.mm"
include "3anbi23d.mm"
include "rspc2ev.mm"
include "syl113anc.mm"
include "rexlimdvva.mm"
include "syld.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "ex.mm"
include "sylbird.mm"
include "ralrimivv.mm"
include "ishaus.mm"

theorem xkohaus
  let cR: class R
  let cS: class S
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x


  assert |- ( ( R e. Top /\ S e. Haus ) -> ( S ^ko R ) e. Haus )

  proof
    cR
    ctop
    wcel
    #
    cS
    cha
    wcel
    #
    wa
    #
    cS
    cR
    cxko
    co
    #
    ctop
    wcel
    #
    vf
    cv
    #
    vg
    cv
    #
    wne
    #
    vf
    vu
    wel
    #
    vg
    vv
    wel
    #
    vu
    cv
    #
    vv
    cv
    #
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vv
    @3
    wrex
    vu
    @3
    wrex
    #
    wi
    #
    vg
    @3
    cuni
    #
    wral
    vf
    @17
    wral
    @3
    cha
    wcel
    @1
    @0
    cS
    ctop
    wcel
    #
    @4
    cS
    haustop
    #
    cR
    cS
    xkotop
    sylan2
    @2
    @16
    vf
    vg
    @17
    @17
    @2
    @5
    @17
    wcel
    #
    @6
    @17
    wcel
    #
    wa
    @5
    cR
    cS
    ccn
    co
    #
    wcel
    #
    @6
    @22
    wcel
    #
    wa
    #
    @16
    @2
    @23
    @20
    @24
    @21
    @2
    @22
    @17
    @5
    @1
    @0
    @18
    @22
    @17
    wceq
    @19
    cR
    cS
    @3
    @3
    eqid
    xkouni
    sylan2
    #
    eleq2d
    @2
    @22
    @17
    @6
    @26
    eleq2d
    anbi12d
    @2
    @25
    @16
    @2
    @25
    wa
    #
    @7
    vx
    cv
    #
    @5
    cfv
    #
    @28
    @6
    cfv
    #
    wceq
    #
    vx
    cR
    cuni
    #
    wral
    #
    wn
    #
    @15
    @27
    @33
    @5
    @6
    @27
    @5
    @32
    wfn
    #
    @6
    @32
    wfn
    #
    vf
    vg
    weq
    @33
    wb
    @27
    @32
    cS
    cuni
    #
    @5
    wf
    #
    @35
    @27
    @23
    @38
    @2
    @23
    @24
    simprl
    #
    @5
    cR
    cS
    @32
    @37
    @32
    eqid
    #
    @37
    eqid
    #
    cnf
    syl
    #
    @32
    @37
    @5
    ffn
    syl
    #
    @27
    @32
    @37
    @6
    wf
    #
    @36
    @27
    @24
    @44
    @2
    @23
    @24
    simprr
    #
    @6
    cR
    cS
    @32
    @37
    @40
    @41
    cnf
    syl
    #
    @32
    @37
    @6
    ffn
    syl
    #
    vx
    @32
    @5
    @6
    eqfnfv
    syl2anc
    necon3abid
    @34
    @31
    wn
    #
    vx
    @32
    wrex
    @27
    @15
    @31
    vx
    @32
    rexnal
    @27
    @48
    @15
    vx
    @32
    @27
    @28
    @32
    wcel
    #
    wa
    #
    @48
    @29
    va
    cv
    #
    wcel
    #
    @30
    vb
    cv
    #
    wcel
    #
    @51
    @53
    cin
    #
    c0
    wceq
    #
    w3a
    #
    vb
    cS
    wrex
    va
    cS
    wrex
    #
    @15
    @48
    @29
    @30
    wne
    #
    @50
    @58
    @29
    @30
    df-ne
    @27
    @49
    @59
    @58
    @27
    @49
    @59
    wa
    #
    wa
    #
    @1
    @29
    @37
    wcel
    @30
    @37
    wcel
    @59
    @58
    @0
    @1
    @25
    @60
    simpllr
    @61
    @32
    @37
    @28
    @5
    @27
    @38
    @60
    @42
    adantr
    @27
    @49
    @59
    simprl
    #
    ffvelrnd
    @61
    @32
    @37
    @28
    @6
    @27
    @44
    @60
    @46
    adantr
    @62
    ffvelrnd
    @27
    @49
    @59
    simprr
    @29
    @30
    vb
    va
    cS
    @37
    @41
    hausnei
    syl13anc
    expr
    syl5bir
    @50
    @57
    @15
    va
    vb
    cS
    cS
    @50
    @51
    cS
    wcel
    #
    @53
    cS
    wcel
    #
    wa
    #
    @57
    @15
    @50
    @65
    @57
    wa
    #
    wa
    #
    vh
    cv
    #
    @28
    csn
    #
    cima
    #
    @51
    wss
    #
    vh
    @22
    crab
    #
    @3
    wcel
    @70
    @53
    wss
    #
    vh
    @22
    crab
    #
    @3
    wcel
    @5
    @72
    wcel
    #
    @6
    @74
    wcel
    #
    @72
    @74
    cin
    #
    c0
    wceq
    #
    @15
    @67
    @69
    cR
    cS
    @51
    vh
    @32
    @40
    @0
    @1
    @25
    @49
    @66
    simp-4l
    #
    @1
    @18
    @0
    @25
    @49
    @66
    @19
    ad4antlr
    #
    @67
    @28
    @32
    @27
    @49
    @66
    simplr
    #
    snssd
    #
    @67
    cR
    @69
    crest
    co
    #
    @69
    cpw
    #
    ccmp
    @67
    cR
    @32
    ctopon
    cfv
    wcel
    #
    @49
    @83
    @84
    wceq
    @67
    @0
    @85
    @79
    cR
    @32
    @40
    toptopon
    sylib
    @81
    @28
    cR
    @32
    restsn2
    syl2anc
    @69
    cfn
    wcel
    @84
    ccmp
    wcel
    @28
    snfi
    @69
    discmp
    mpbi
    syl6eqel
    #
    @50
    @63
    @64
    @57
    simprll
    xkoopn
    @67
    @69
    cR
    cS
    @53
    vh
    @32
    @40
    @79
    @80
    @82
    @86
    @50
    @63
    @64
    @57
    simprlr
    xkoopn
    @67
    @23
    @5
    @69
    cima
    #
    @51
    wss
    #
    @75
    @27
    @23
    @49
    @66
    @39
    ad2antrr
    @67
    @87
    @29
    csn
    #
    @51
    @67
    @35
    @49
    @89
    @87
    wceq
    @27
    @35
    @49
    @66
    @43
    ad2antrr
    @81
    @32
    @28
    @5
    fnsnfv
    syl2anc
    @67
    @29
    @51
    @52
    @54
    @56
    @65
    @50
    simprr1
    snssd
    eqsstr3d
    @71
    @88
    vh
    @5
    @22
    vh
    vf
    weq
    @70
    @87
    @51
    @68
    @5
    @69
    imaeq1
    sseq1d
    elrab
    sylanbrc
    @67
    @24
    @6
    @69
    cima
    #
    @53
    wss
    #
    @76
    @27
    @24
    @49
    @66
    @45
    ad2antrr
    @67
    @90
    @30
    csn
    #
    @53
    @67
    @36
    @49
    @92
    @90
    wceq
    @27
    @36
    @49
    @66
    @47
    ad2antrr
    @81
    @32
    @28
    @6
    fnsnfv
    syl2anc
    @67
    @30
    @53
    @52
    @54
    @56
    @65
    @50
    simprr2
    snssd
    eqsstr3d
    @73
    @91
    vh
    @6
    @22
    vh
    vg
    weq
    @70
    @90
    @53
    @68
    @6
    @69
    imaeq1
    sseq1d
    elrab
    sylanbrc
    @67
    @77
    @71
    @73
    wa
    #
    vh
    @22
    crab
    #
    c0
    @71
    @73
    vh
    @22
    inrab
    @67
    @93
    wn
    #
    vh
    @22
    wral
    @94
    c0
    wceq
    @67
    @95
    vh
    @22
    @67
    @68
    @22
    wcel
    #
    wa
    #
    @70
    @55
    wss
    #
    @93
    @97
    @98
    @28
    @68
    cdm
    #
    wcel
    #
    @97
    @28
    @32
    @99
    @27
    @49
    @66
    @96
    simpllr
    @96
    @99
    @32
    wceq
    #
    @67
    @96
    @32
    @37
    @68
    wf
    @101
    @68
    cR
    cS
    @32
    @37
    @40
    @41
    cnf
    @32
    @37
    @68
    fdm
    syl
    adantl
    eleqtrrd
    @97
    @98
    @70
    c0
    wceq
    #
    @100
    wn
    #
    @97
    @56
    @98
    @102
    wi
    @67
    @56
    @96
    @52
    @54
    @56
    @65
    @50
    simprr3
    adantr
    @98
    @56
    @102
    @70
    @55
    sseq0
    expcom
    syl
    @102
    @99
    @69
    cin
    c0
    wceq
    @103
    @68
    @69
    imadisj
    @99
    @28
    disjsn
    bitri
    syl6ib
    mt2d
    @70
    @51
    @53
    ssin
    sylnibr
    ralrimiva
    @93
    vh
    @22
    rabeq0
    sylibr
    syl5eq
    @14
    @75
    @76
    @78
    w3a
    @75
    @9
    @72
    @11
    cin
    #
    c0
    wceq
    #
    w3a
    vu
    vv
    @72
    @74
    @3
    @3
    @10
    @72
    wceq
    #
    @8
    @75
    @13
    @105
    @9
    @10
    @72
    @5
    eleq2
    @106
    @12
    @104
    c0
    @10
    @72
    @11
    ineq1
    eqeq1d
    3anbi13d
    @11
    @74
    wceq
    #
    @9
    @76
    @105
    @78
    @75
    @11
    @74
    @6
    eleq2
    @107
    @104
    @77
    c0
    @11
    @74
    @72
    ineq2
    eqeq1d
    3anbi23d
    rspc2ev
    syl113anc
    expr
    rexlimdvva
    syld
    rexlimdva
    syl5bir
    sylbid
    ex
    sylbird
    ralrimivv
    vf
    vg
    vv
    vu
    @3
    @17
    @17
    eqid
    ishaus
    sylanbrc
end
