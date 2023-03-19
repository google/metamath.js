include "com.mm"
include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "csuc.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wral.mm"
include "crn.mm"
include "wpo.mm"
include "w3a.mm"
include "weq.mm"
include "w3o.mm"
include "wor.mm"
include "simp3.mm"
include "wcel.mm"
include "wa.mm"
include "wrex.mm"
include "wb.mm"
include "fvelrnb.mm"
include "anbi12d.mm"
include "3ad2ant1.mm"
include "reeanv.mm"
include "wss.mm"
include "word.mm"
include "nnord.mm"
include "ordtri2or2.mm"
include "syl2an.mm"
include "adantl.mm"
include "wi.mm"
include "vex.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "anbi2d.mm"
include "sseq12.mm"
include "fveq2.mm"
include "breqan12d.mm"
include "eqeqan12d.mm"
include "orbi12d.mm"
include "imbi12d.mm"
include "breq2d.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "eqid.mm"
include "olci.mm"
include "2a1i.mm"
include "simplll.mm"
include "simpr2.mm"
include "suceq.mm"
include "fveq2d.mm"
include "breq12d.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "simprr.mm"
include "simprl.mm"
include "simpllr.mm"
include "fnfvelrn.mm"
include "peano2.mm"
include "ad3antrrr.mm"
include "potr.mm"
include "syl13anc.mm"
include "imp.mm"
include "ancom2s.mm"
include "orcd.mm"
include "expr.mm"
include "breq1.mm"
include "biimprcd.mm"
include "orc.mm"
include "syl6.mm"
include "jaod.mm"
include "ex.mm"
include "breq2.mm"
include "eqeq2.mm"
include "biimpd.mm"
include "a1i.mm"
include "3adantr2.mm"
include "mpd.mm"
include "a2d.mm"
include "findsg.mm"
include "ancom1s.mm"
include "impcom.mm"
include "vtocl2.mm"
include "orim12d.mm"
include "3mix1.mm"
include "3mix2.mm"
include "jaoi.mm"
include "3mix3.mm"
include "eqcoms.mm"
include "syl.mm"
include "breq12.mm"
include "eqeq12.mm"
include "ancoms.mm"
include "3orbi123d.mm"
include "syl5ibcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "ralrimivv.mm"
include "df-so.mm"
include "sylanbrc.mm"

theorem sornom
  let cR: class R
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e

  disjoint F a
  disjoint R a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F e
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint c d
  disjoint c e
  disjoint d e
  disjoint R b
  disjoint R c
  disjoint R d
  disjoint R e
  assert |- ( ( F Fn _om /\ A. a e. _om ( ( F ` a ) R ( F ` suc a ) \/ ( F ` a ) = ( F ` suc a ) ) /\ R Po ran F ) -> R Or ran F )

  proof
    cF
    com
    wfn
    #
    va
    cv
    #
    cF
    cfv
    #
    @1
    csuc
    #
    cF
    cfv
    #
    cR
    wbr
    #
    @2
    @4
    wceq
    #
    wo
    #
    va
    com
    wral
    #
    cF
    crn
    #
    cR
    wpo
    #
    w3a
    #
    @10
    vb
    cv
    #
    vc
    cv
    #
    cR
    wbr
    #
    vb
    vc
    weq
    #
    @13
    @12
    cR
    wbr
    #
    w3o
    #
    vc
    @9
    wral
    vb
    @9
    wral
    @9
    cR
    wor
    @0
    @8
    @10
    simp3
    @11
    @17
    vb
    vc
    @9
    @9
    @11
    @12
    @9
    wcel
    #
    @13
    @9
    wcel
    #
    wa
    #
    vd
    cv
    #
    cF
    cfv
    #
    @12
    wceq
    #
    vd
    com
    wrex
    #
    ve
    cv
    #
    cF
    cfv
    #
    @13
    wceq
    #
    ve
    com
    wrex
    #
    wa
    #
    @17
    @0
    @8
    @20
    @29
    wb
    @10
    @0
    @18
    @24
    @19
    @28
    vd
    com
    @12
    cF
    fvelrnb
    ve
    com
    @13
    cF
    fvelrnb
    anbi12d
    3ad2ant1
    @29
    @23
    @27
    wa
    #
    ve
    com
    wrex
    vd
    com
    wrex
    @11
    @17
    @23
    @27
    vd
    ve
    com
    com
    reeanv
    @11
    @30
    @17
    vd
    ve
    com
    com
    @11
    @21
    com
    wcel
    #
    @25
    com
    wcel
    #
    wa
    #
    wa
    #
    @22
    @26
    cR
    wbr
    #
    @22
    @26
    wceq
    #
    @26
    @22
    cR
    wbr
    #
    w3o
    #
    @30
    @17
    @34
    @35
    @36
    wo
    #
    @37
    @26
    @22
    wceq
    #
    wo
    #
    wo
    #
    @38
    @34
    @21
    @25
    wss
    #
    @25
    @21
    wss
    #
    wo
    #
    @42
    @33
    @45
    @11
    @31
    @21
    word
    @25
    word
    @45
    @32
    @21
    nnord
    @25
    nnord
    @21
    @25
    ordtri2or2
    syl2an
    adantl
    @34
    @43
    @39
    @44
    @41
    @11
    @12
    com
    wcel
    #
    @13
    com
    wcel
    #
    wa
    #
    wa
    #
    @12
    @13
    wss
    #
    @12
    cF
    cfv
    #
    @13
    cF
    cfv
    #
    cR
    wbr
    #
    @51
    @52
    wceq
    #
    wo
    #
    wi
    #
    wi
    #
    @34
    @43
    @39
    wi
    #
    wi
    vb
    vc
    @21
    @25
    vd
    vex
    #
    ve
    vex
    #
    vb
    vd
    weq
    #
    vc
    ve
    weq
    #
    wa
    #
    @49
    @34
    @56
    @58
    @63
    @48
    @33
    @11
    @61
    @46
    @31
    @62
    @47
    @32
    @12
    @21
    com
    eleq1
    @13
    @25
    com
    eleq1
    bi2anan9
    anbi2d
    @63
    @50
    @43
    @55
    @39
    @12
    @21
    @13
    @25
    sseq12
    @63
    @53
    @35
    @54
    @36
    @61
    @62
    @51
    @22
    @52
    @26
    cR
    @12
    @21
    cF
    fveq2
    #
    @13
    @25
    cF
    fveq2
    #
    breqan12d
    @61
    @62
    @51
    @22
    @52
    @26
    @64
    @65
    eqeqan12d
    orbi12d
    imbi12d
    imbi12d
    @11
    @48
    @50
    @55
    @48
    @50
    wa
    @11
    @55
    @47
    @46
    @50
    @11
    @55
    wi
    #
    @11
    @51
    @22
    cR
    wbr
    #
    @51
    @22
    wceq
    #
    wo
    #
    wi
    @11
    @51
    @51
    cR
    wbr
    #
    @51
    @51
    wceq
    #
    wo
    #
    wi
    @11
    @51
    @26
    cR
    wbr
    #
    @51
    @26
    wceq
    #
    wo
    #
    wi
    @11
    @51
    @25
    csuc
    #
    cF
    cfv
    #
    cR
    wbr
    #
    @51
    @77
    wceq
    #
    wo
    #
    wi
    @66
    vd
    ve
    @13
    @12
    vd
    vb
    weq
    #
    @69
    @72
    @11
    @81
    @67
    @70
    @68
    @71
    @81
    @22
    @51
    @51
    cR
    @21
    @12
    cF
    fveq2
    #
    breq2d
    @81
    @22
    @51
    @51
    @82
    eqeq2d
    orbi12d
    imbi2d
    vd
    ve
    weq
    #
    @69
    @75
    @11
    @83
    @67
    @73
    @68
    @74
    @83
    @22
    @26
    @51
    cR
    @21
    @25
    cF
    fveq2
    #
    breq2d
    @83
    @22
    @26
    @51
    @84
    eqeq2d
    orbi12d
    imbi2d
    @21
    @76
    wceq
    #
    @69
    @80
    @11
    @85
    @67
    @78
    @68
    @79
    @85
    @22
    @77
    @51
    cR
    @21
    @76
    cF
    fveq2
    #
    breq2d
    @85
    @22
    @77
    @51
    @86
    eqeq2d
    orbi12d
    imbi2d
    vd
    vc
    weq
    #
    @69
    @55
    @11
    @87
    @67
    @53
    @68
    @54
    @87
    @22
    @52
    @51
    cR
    @21
    @13
    cF
    fveq2
    #
    breq2d
    @87
    @22
    @52
    @51
    @88
    eqeq2d
    orbi12d
    imbi2d
    @72
    @46
    @11
    @71
    @70
    @51
    eqid
    olci
    2a1i
    @32
    @46
    wa
    @12
    @25
    wss
    #
    wa
    #
    @11
    @75
    @80
    @90
    @11
    @75
    @80
    wi
    #
    @90
    @11
    wa
    #
    @26
    @77
    cR
    wbr
    #
    @26
    @77
    wceq
    #
    wo
    #
    @91
    @92
    @32
    @8
    @95
    @32
    @46
    @89
    @11
    simplll
    @90
    @0
    @8
    @10
    simpr2
    @7
    @95
    va
    @25
    com
    va
    ve
    weq
    #
    @5
    @93
    @6
    @94
    @96
    @2
    @26
    @4
    @77
    cR
    @1
    @25
    cF
    fveq2
    #
    @96
    @3
    @76
    cF
    @1
    @25
    suceq
    fveq2d
    #
    breq12d
    @96
    @2
    @26
    @4
    @77
    @97
    @98
    eqeq12d
    orbi12d
    rspcva
    syl2anc
    @90
    @0
    @10
    @95
    @91
    wi
    @8
    @90
    @0
    @10
    wa
    #
    wa
    #
    @93
    @91
    @94
    @100
    @93
    @91
    @100
    @93
    wa
    @73
    @80
    @74
    @100
    @93
    @73
    @80
    @100
    @93
    @73
    wa
    wa
    @78
    @79
    @100
    @73
    @93
    @78
    @100
    @73
    @93
    wa
    #
    @78
    @100
    @10
    @51
    @9
    wcel
    #
    @26
    @9
    wcel
    #
    @77
    @9
    wcel
    #
    @101
    @78
    wi
    @90
    @0
    @10
    simprr
    @100
    @0
    @46
    @102
    @90
    @0
    @10
    simprl
    #
    @32
    @46
    @89
    @99
    simpllr
    com
    @12
    cF
    fnfvelrn
    syl2anc
    @100
    @0
    @32
    @103
    @105
    @32
    @46
    @89
    @99
    simplll
    com
    @25
    cF
    fnfvelrn
    syl2anc
    @100
    @0
    @76
    com
    wcel
    #
    @104
    @105
    @32
    @106
    @46
    @89
    @99
    @25
    peano2
    ad3antrrr
    com
    @76
    cF
    fnfvelrn
    syl2anc
    @9
    @51
    @26
    @77
    cR
    potr
    syl13anc
    imp
    ancom2s
    orcd
    expr
    @93
    @74
    @80
    wi
    @100
    @93
    @74
    @78
    @80
    @74
    @78
    @93
    @51
    @26
    @77
    cR
    breq1
    biimprcd
    @78
    @79
    orc
    syl6
    adantl
    jaod
    ex
    @94
    @91
    wi
    @100
    @94
    @75
    @80
    @94
    @73
    @78
    @74
    @79
    @26
    @77
    @51
    cR
    breq2
    @26
    @77
    @51
    eqeq2
    orbi12d
    biimpd
    a1i
    jaod
    3adantr2
    mpd
    ex
    a2d
    findsg
    ancom1s
    impcom
    expr
    #
    vtocl2
    @11
    @32
    @31
    @44
    @41
    wi
    #
    @57
    @11
    @32
    @31
    wa
    #
    wa
    #
    @108
    wi
    vb
    vc
    @25
    @21
    @60
    @59
    vb
    ve
    weq
    #
    vc
    vd
    weq
    #
    wa
    #
    @49
    @110
    @56
    @108
    @113
    @48
    @109
    @11
    @111
    @46
    @32
    @112
    @47
    @31
    @12
    @25
    com
    eleq1
    @13
    @21
    com
    eleq1
    bi2anan9
    anbi2d
    @113
    @50
    @44
    @55
    @41
    @12
    @25
    @13
    @21
    sseq12
    @113
    @53
    @37
    @54
    @40
    @111
    @112
    @51
    @26
    @52
    @22
    cR
    @12
    @25
    cF
    fveq2
    #
    @13
    @21
    cF
    fveq2
    #
    breqan12d
    @111
    @112
    @51
    @26
    @52
    @22
    @114
    @115
    eqeqan12d
    orbi12d
    imbi12d
    imbi12d
    @107
    vtocl2
    ancom2s
    orim12d
    mpd
    @39
    @38
    @41
    @35
    @38
    @36
    @35
    @36
    @37
    3mix1
    @36
    @35
    @37
    3mix2
    #
    jaoi
    @37
    @38
    @40
    @37
    @35
    @36
    3mix3
    @38
    @22
    @26
    @116
    eqcoms
    jaoi
    jaoi
    syl
    @30
    @35
    @14
    @36
    @15
    @37
    @16
    @22
    @12
    @26
    @13
    cR
    breq12
    @22
    @12
    @26
    @13
    eqeq12
    @27
    @23
    @37
    @16
    wb
    @26
    @13
    @22
    @12
    cR
    breq12
    ancoms
    3orbi123d
    syl5ibcom
    rexlimdvva
    syl5bir
    sylbid
    ralrimivv
    vb
    vc
    @9
    cR
    df-so
    sylanbrc
end
