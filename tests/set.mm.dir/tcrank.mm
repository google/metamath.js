include "cr1.mm"
include "con0.mm"
include "cima.mm"
include "cuni.mm"
include "wcel.mm"
include "crnk.mm"
include "cfv.mm"
include "ctc.mm"
include "cv.mm"
include "csuc.mm"
include "wrex.mm"
include "wss.mm"
include "rankwflemb.mm"
include "wral.mm"
include "wi.mm"
include "suceloni.mm"
include "weq.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "imaeq2d.mm"
include "sseq12d.mm"
include "cbvralv.mm"
include "syl6bb.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "simpr.mm"
include "simprl.mm"
include "simplr.mm"
include "rankr1ai.mm"
include "rspcv.mm"
include "syl.mm"
include "r1elwf.mm"
include "r1rankidb.mm"
include "ssralv.mm"
include "3syl.mm"
include "syld.mm"
include "sylc.mm"
include "crab.mm"
include "cint.mm"
include "rankval3b.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "rankon.mm"
include "oneli.mm"
include "eleq2.mm"
include "ralbidv.mm"
include "onnminsb.mm"
include "sylcom.mm"
include "imp.mm"
include "rexnal.mm"
include "sylibr.mm"
include "adantl.mm"
include "r19.29.mm"
include "syl2anc.mm"
include "w3a.mm"
include "simp2.mm"
include "cvv.mm"
include "vex.mm"
include "tcid.mm"
include "ax-mp.mm"
include "sseli.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "ex.mm"
include "simp3l.mm"
include "sseld.mm"
include "simp1l.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "rankf.mm"
include "ffn.mm"
include "wtr.mm"
include "r1tr.mm"
include "trel.mm"
include "tcwf.mm"
include "fvex.mm"
include "r1elss.mm"
include "sylib.mm"
include "fvelimab.mm"
include "sylancr.mm"
include "tcel.mm"
include "ssrexv.mm"
include "adantr.mm"
include "sylbid.mm"
include "wo.mm"
include "w3o.mm"
include "word.mm"
include "eloni.mm"
include "ordtri3or.mm"
include "syl2an.mm"
include "3orass.mm"
include "orcanai.mm"
include "ad2ant2l.mm"
include "3adant2.mm"
include "mpjaod.mm"
include "rexlimdv3a.mm"
include "expr.mm"
include "r1elssi.mm"
include "sylan2.mm"
include "sylibrd.mm"
include "ssrdv.mm"
include "ralrimiva.mm"
include "tfis3.mm"
include "rspccv.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "cab.mm"
include "tcvalg.mm"
include "sseq2.mm"
include "treq.mm"
include "anbi12d.mm"
include "elab.mm"
include "intss1.mm"
include "sylbir.mm"
include "sylancl.mm"
include "eqsstrd.mm"
include "imass2.mm"
include "wfun.mm"
include "ffun.mm"
include "fvelima.mm"
include "mpan.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "ssriv.mm"
include "syl6ss.mm"
include "eqssd.mm"

theorem tcrank
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u


  assert |- ( A e. U. ( R1 " On ) -> ( rank ` A ) = ( rank " ( TC ` A ) ) )

  proof
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cA
    crnk
    cfv
    #
    crnk
    cA
    ctc
    cfv
    #
    cima
    #
    @1
    cA
    vy
    cv
    #
    csuc
    #
    cr1
    cfv
    #
    wcel
    #
    vy
    con0
    wrex
    @2
    @4
    wss
    #
    vy
    cA
    rankwflemb
    @8
    @9
    vy
    con0
    @5
    con0
    wcel
    @6
    con0
    wcel
    vz
    cv
    #
    crnk
    cfv
    #
    crnk
    @10
    ctc
    cfv
    #
    cima
    #
    wss
    #
    vz
    @7
    wral
    #
    @8
    @9
    wi
    @5
    suceloni
    @14
    vz
    vx
    cv
    #
    cr1
    cfv
    #
    wral
    #
    vu
    cv
    #
    crnk
    cfv
    #
    crnk
    @19
    ctc
    cfv
    #
    cima
    #
    wss
    #
    vu
    @5
    cr1
    cfv
    #
    wral
    #
    @15
    vx
    vy
    @6
    vx
    vy
    weq
    #
    @18
    @14
    vz
    @24
    wral
    @25
    @26
    @14
    vz
    @17
    @24
    @16
    @5
    cr1
    fveq2
    raleqdv
    @14
    @23
    vz
    vu
    @24
    vz
    vu
    weq
    #
    @11
    @20
    @13
    @22
    @10
    @19
    crnk
    fveq2
    @27
    @12
    @21
    crnk
    @10
    @19
    ctc
    fveq2
    imaeq2d
    sseq12d
    cbvralv
    syl6bb
    @16
    @6
    wceq
    @14
    vz
    @17
    @7
    @16
    @6
    cr1
    fveq2
    raleqdv
    @16
    con0
    wcel
    #
    @25
    vy
    @16
    wral
    #
    @18
    @28
    @29
    wa
    #
    @14
    vz
    @17
    @30
    @10
    @17
    wcel
    #
    wa
    #
    vw
    @11
    @13
    @32
    vw
    cv
    #
    @11
    wcel
    #
    @16
    crnk
    cfv
    #
    @33
    wceq
    #
    vx
    @12
    wrex
    #
    @33
    @13
    wcel
    #
    @30
    @31
    @34
    @37
    @30
    @31
    @34
    wa
    #
    wa
    #
    @39
    @23
    @20
    @33
    wcel
    #
    wn
    #
    wa
    #
    vu
    @10
    wrex
    #
    @37
    @30
    @39
    simpr
    @40
    @23
    vu
    @10
    wral
    #
    @42
    vu
    @10
    wrex
    #
    @44
    @40
    @31
    @29
    @45
    @30
    @31
    @34
    simprl
    @28
    @29
    @39
    simplr
    @31
    @29
    @23
    vu
    @11
    cr1
    cfv
    #
    wral
    #
    @45
    @31
    @11
    @16
    wcel
    @29
    @48
    wi
    @10
    @16
    rankr1ai
    @25
    @48
    vy
    @11
    @16
    @5
    @11
    wceq
    @23
    vu
    @24
    @47
    @5
    @11
    cr1
    fveq2
    raleqdv
    rspcv
    syl
    @31
    @10
    @0
    wcel
    #
    @10
    @47
    wss
    @48
    @45
    wi
    @10
    @16
    r1elwf
    #
    @10
    r1rankidb
    @23
    vu
    @10
    @47
    ssralv
    3syl
    syld
    sylc
    @39
    @46
    @30
    @39
    @41
    vu
    @10
    wral
    #
    wn
    #
    @46
    @31
    @34
    @52
    @31
    @49
    @34
    @52
    wi
    @50
    @49
    @34
    @33
    @20
    @16
    wcel
    #
    vu
    @10
    wral
    #
    vx
    con0
    crab
    cint
    #
    wcel
    #
    @52
    @49
    @34
    @56
    @49
    @11
    @55
    @33
    vx
    vu
    @10
    rankval3b
    eleq2d
    biimpd
    @34
    @33
    con0
    wcel
    #
    @56
    @52
    wi
    @11
    @33
    @10
    rankon
    oneli
    #
    @54
    @51
    vx
    @33
    vx
    vw
    weq
    @53
    @41
    vu
    @10
    @16
    @33
    @20
    eleq2
    ralbidv
    onnminsb
    syl
    sylcom
    syl
    imp
    @41
    vu
    @10
    rexnal
    sylibr
    adantl
    @23
    @42
    vu
    @10
    r19.29
    syl2anc
    @39
    @43
    @37
    vu
    @10
    @39
    @19
    @10
    wcel
    #
    @43
    w3a
    #
    @20
    @33
    wceq
    #
    @37
    @33
    @20
    wcel
    #
    @60
    @59
    @19
    @12
    wcel
    #
    @61
    @37
    wi
    @39
    @59
    @43
    simp2
    #
    @10
    @12
    @19
    @10
    cvv
    wcel
    @10
    @12
    wss
    vz
    vex
    #
    @10
    cvv
    tcid
    ax-mp
    sseli
    @63
    @61
    @37
    @36
    @61
    vx
    @19
    @12
    vx
    vu
    weq
    @35
    @20
    @33
    @16
    @19
    crnk
    fveq2
    eqeq1d
    rspcev
    ex
    3syl
    @60
    @62
    @33
    @22
    wcel
    #
    @37
    @60
    @20
    @22
    @33
    @39
    @59
    @23
    @42
    simp3l
    sseld
    @60
    @59
    @31
    @66
    @37
    wi
    @64
    @31
    @34
    @59
    @43
    simp1l
    @59
    @31
    wa
    #
    @66
    @36
    vx
    @21
    wrex
    #
    @37
    @67
    crnk
    @0
    wfn
    #
    @21
    @0
    wss
    #
    @66
    @68
    wb
    @0
    con0
    crnk
    wf
    #
    @69
    rankf
    @0
    con0
    crnk
    ffn
    ax-mp
    #
    @67
    @19
    @17
    wcel
    #
    @19
    @0
    wcel
    #
    @70
    @17
    wtr
    @67
    @73
    wi
    @16
    r1tr
    @17
    @19
    @10
    trel
    ax-mp
    @19
    @16
    r1elwf
    @74
    @21
    @0
    wcel
    @70
    @19
    tcwf
    @21
    @19
    ctc
    fvex
    r1elss
    sylib
    3syl
    vx
    @0
    @21
    @33
    crnk
    fvelimab
    sylancr
    @59
    @68
    @37
    wi
    #
    @31
    @59
    @21
    @12
    wss
    @75
    @10
    @19
    @65
    tcel
    @36
    vx
    @21
    @12
    ssrexv
    syl
    adantr
    sylbid
    syl2anc
    syld
    @39
    @43
    @61
    @62
    wo
    #
    @59
    @34
    @42
    @76
    @31
    @23
    @34
    @41
    @76
    @34
    @41
    @61
    @62
    w3o
    #
    @41
    @76
    wo
    @34
    @20
    con0
    wcel
    #
    @57
    @77
    @19
    rankon
    @58
    @78
    @20
    word
    @33
    word
    @77
    @57
    @20
    eloni
    @33
    eloni
    @20
    @33
    ordtri3or
    syl2an
    sylancr
    @41
    @61
    @62
    3orass
    sylib
    orcanai
    ad2ant2l
    3adant2
    mpjaod
    rexlimdv3a
    sylc
    expr
    @31
    @38
    @37
    wb
    #
    @30
    @31
    @49
    @79
    @50
    @49
    @69
    @12
    @0
    wcel
    #
    @79
    @72
    @10
    tcwf
    @80
    @69
    @12
    @0
    wss
    @79
    @12
    r1elssi
    vx
    @0
    @12
    @33
    crnk
    fvelimab
    sylan2
    sylancr
    syl
    adantl
    sylibrd
    ssrdv
    ralrimiva
    ex
    tfis3
    @14
    @9
    vz
    cA
    @7
    @10
    cA
    wceq
    #
    @11
    @2
    @13
    @4
    @10
    cA
    crnk
    fveq2
    @81
    @12
    @3
    crnk
    @10
    cA
    ctc
    fveq2
    imaeq2d
    sseq12d
    rspccv
    3syl
    rexlimiv
    sylbi
    @1
    @3
    @2
    cr1
    cfv
    #
    wss
    #
    @4
    @2
    wss
    @1
    @3
    cA
    @16
    wss
    #
    @16
    wtr
    #
    wa
    #
    vx
    cab
    #
    cint
    #
    @82
    vx
    cA
    @0
    tcvalg
    @1
    cA
    @82
    wss
    #
    @82
    wtr
    #
    @88
    @82
    wss
    #
    cA
    r1rankidb
    @2
    r1tr
    @89
    @90
    wa
    #
    @82
    @87
    wcel
    @91
    @86
    @92
    vx
    @82
    @2
    cr1
    fvex
    @16
    @82
    wceq
    @84
    @89
    @85
    @90
    @16
    @82
    cA
    sseq2
    @16
    @82
    treq
    anbi12d
    elab
    @82
    @87
    intss1
    sylbir
    sylancl
    eqsstrd
    @83
    @4
    crnk
    @82
    cima
    #
    @2
    @3
    @82
    crnk
    imass2
    vx
    @93
    @2
    @16
    @93
    wcel
    #
    @5
    crnk
    cfv
    #
    @16
    wceq
    #
    vy
    @82
    wrex
    #
    @16
    @2
    wcel
    #
    crnk
    wfun
    #
    @94
    @97
    @71
    @99
    rankf
    @0
    con0
    crnk
    ffun
    ax-mp
    vy
    @16
    @82
    crnk
    fvelima
    mpan
    @96
    @98
    vy
    @82
    @5
    @82
    wcel
    @95
    @2
    wcel
    @96
    @98
    @5
    @2
    rankr1ai
    @95
    @16
    @2
    eleq1
    syl5ibcom
    rexlimiv
    syl
    ssriv
    syl6ss
    syl
    eqssd
end
