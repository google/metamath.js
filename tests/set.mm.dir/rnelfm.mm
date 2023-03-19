include "wcel.mm"
include "cfil.mm"
include "cfv.mm"
include "wf.mm"
include "w3a.mm"
include "cfm.mm"
include "co.mm"
include "crn.mm"
include "cv.mm"
include "wceq.mm"
include "cfbas.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "filtop.mm"
include "3ad2ant2.mm"
include "simp1.mm"
include "simp3.mm"
include "fmf.mm"
include "syl3anc.mm"
include "ffn.mm"
include "syl.mm"
include "fvelrnb.mm"
include "wi.mm"
include "wa.mm"
include "cima.mm"
include "wfo.mm"
include "dffn4.mm"
include "sylib.mm"
include "foima.mm"
include "ad2antlr.mm"
include "cfg.mm"
include "simpll.mm"
include "simpr.mm"
include "simplr.mm"
include "fgcl.mm"
include "adantl.mm"
include "eqid.mm"
include "imaelfm.mm"
include "syl31anc.mm"
include "eqeltrrd.mm"
include "eleq2.mm"
include "syl5ibcom.mm"
include "ex.mm"
include "sylan.mm"
include "3adant1.mm"
include "rexlimdv.mm"
include "sylbid.mm"
include "ccnv.mm"
include "cmpt.mm"
include "wss.mm"
include "simpl2.mm"
include "filelss.mm"
include "eqidd.mm"
include "imaeq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "cvv.mm"
include "simpl1.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "3ad2ant3.mm"
include "adantr.mm"
include "ssexd.mm"
include "elrnmpt.mm"
include "mpbird.mm"
include "ssid.mm"
include "wfun.mm"
include "ffun.mm"
include "ad2antrr.mm"
include "funimass3.mm"
include "sylancl.mm"
include "mpbiri.mm"
include "sseq1d.mm"
include "jcad.mm"
include "vex.mm"
include "ax-mp.mm"
include "cin.mm"
include "ad3antrrr.mm"
include "imassrn.mm"
include "ssin.mm"
include "sylanblc.mm"
include "elin.mm"
include "jctir.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "fvimacnv.mm"
include "biimpa.mm"
include "funfvima2.mm"
include "sylc.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "rexlimdva.mm"
include "com23.mm"
include "impd.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "filin.mm"
include "3exp.mm"
include "imp31.mm"
include "eqeltrd.mm"
include "exp32.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "syl5ibrcom.mm"
include "imp44.mm"
include "simprr.mm"
include "simprlr.mm"
include "filss.mm"
include "syl13anc.mm"
include "exp44.mm"
include "impbid.mm"
include "rnelfmlem.mm"
include "simpl3.mm"
include "elfm.mm"
include "bitr4d.mm"
include "eqrdv.mm"
include "fnfvelrn.mm"

theorem rnelfm
  let cA: class A
  let cF: class F
  let cL: class L
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( Y e. A /\ L e. ( Fil ` X ) /\ F : Y --> X ) -> ( L e. ran ( X FilMap F ) <-> ran F e. L ) )

  proof
    cY
    cA
    wcel
    #
    cL
    cX
    cfil
    cfv
    #
    wcel
    #
    cY
    cX
    cF
    wf
    #
    w3a
    #
    cL
    cX
    cF
    cfm
    co
    #
    crn
    #
    wcel
    #
    cF
    crn
    #
    cL
    wcel
    #
    @4
    @7
    vb
    cv
    #
    @5
    cfv
    #
    cL
    wceq
    #
    vb
    cY
    cfbas
    cfv
    #
    wrex
    #
    @9
    @4
    @5
    @13
    wfn
    #
    @7
    @14
    wb
    @4
    @13
    @1
    @5
    wf
    #
    @15
    @4
    cX
    cL
    wcel
    #
    @0
    @3
    @16
    @2
    @0
    @17
    @3
    cL
    cX
    filtop
    #
    3ad2ant2
    #
    @0
    @2
    @3
    simp1
    @0
    @2
    @3
    simp3
    cL
    cA
    cF
    cX
    cY
    fmf
    syl3anc
    @13
    @1
    @5
    ffn
    syl
    #
    vb
    @13
    cL
    @5
    fvelrnb
    syl
    @4
    @12
    @9
    vb
    @13
    @2
    @3
    @10
    @13
    wcel
    #
    @12
    @9
    wi
    #
    wi
    #
    @0
    @2
    @17
    @3
    @23
    @18
    @17
    @3
    wa
    #
    @21
    @22
    @24
    @21
    wa
    #
    @8
    @11
    wcel
    @12
    @9
    @25
    cF
    cY
    cima
    #
    @8
    @11
    @3
    @26
    @8
    wceq
    #
    @17
    @21
    @3
    cY
    @8
    cF
    wfo
    #
    @27
    @3
    cF
    cY
    wfn
    #
    @28
    cY
    cX
    cF
    ffn
    #
    cY
    cF
    dffn4
    sylib
    cY
    @8
    cF
    foima
    syl
    ad2antlr
    @25
    @17
    @21
    @3
    cY
    cY
    @10
    cfg
    co
    #
    wcel
    #
    @26
    @11
    wcel
    @17
    @3
    @21
    simpll
    @24
    @21
    simpr
    @17
    @3
    @21
    simplr
    @21
    @32
    @24
    @21
    @31
    cY
    cfil
    cfv
    wcel
    @32
    @10
    cY
    fgcl
    @31
    cY
    filtop
    syl
    adantl
    cL
    @10
    cY
    cF
    @31
    cX
    cY
    @31
    eqid
    imaelfm
    syl31anc
    eqeltrrd
    @11
    cL
    @8
    eleq2
    syl5ibcom
    ex
    sylan
    3adant1
    rexlimdv
    sylbid
    @4
    @9
    @7
    @4
    @9
    wa
    #
    cL
    vx
    cL
    cF
    ccnv
    #
    vx
    cv
    #
    cima
    #
    cmpt
    #
    crn
    #
    @5
    cfv
    #
    @6
    @33
    vt
    cL
    @39
    @33
    vt
    cv
    #
    cL
    wcel
    #
    @40
    cX
    wss
    #
    cF
    vs
    cv
    #
    cima
    #
    @40
    wss
    #
    vs
    @38
    wrex
    #
    wa
    #
    @40
    @39
    wcel
    #
    @33
    @41
    @47
    @33
    @41
    @42
    @46
    @33
    @2
    @41
    @42
    wi
    @0
    @2
    @3
    @9
    simpl2
    #
    @2
    @41
    @42
    @40
    cL
    cX
    filelss
    ex
    syl
    @33
    @41
    @46
    @33
    @41
    wa
    #
    @34
    @40
    cima
    #
    @38
    wcel
    #
    cF
    @51
    cima
    #
    @40
    wss
    #
    @46
    @50
    @52
    @51
    @36
    wceq
    #
    vx
    cL
    wrex
    #
    @50
    @41
    @51
    @51
    wceq
    #
    @56
    @33
    @41
    simpr
    @50
    @51
    eqidd
    @55
    @57
    vx
    @40
    cL
    @35
    @40
    wceq
    @36
    @51
    @51
    @35
    @40
    @34
    imaeq2
    eqeq2d
    rspcev
    syl2anc
    @33
    @52
    @56
    wb
    #
    @41
    @33
    @51
    cvv
    wcel
    @58
    @33
    @51
    cY
    cA
    @0
    @2
    @3
    @9
    simpl1
    @4
    @51
    cY
    wss
    #
    @9
    @3
    @0
    @59
    @2
    @3
    cF
    cdm
    #
    @51
    cY
    cF
    @40
    cnvimass
    #
    cY
    cX
    cF
    fdm
    #
    syl5sseq
    3ad2ant3
    adantr
    ssexd
    vx
    cL
    @36
    @51
    @37
    cvv
    @37
    eqid
    #
    elrnmpt
    syl
    adantr
    mpbird
    @50
    @54
    @51
    @51
    wss
    #
    @51
    ssid
    @50
    cF
    wfun
    #
    @51
    @60
    wss
    @54
    @64
    wb
    @4
    @65
    @9
    @41
    @3
    @0
    @65
    @2
    cY
    cX
    cF
    ffun
    3ad2ant3
    #
    ad2antrr
    @61
    @51
    @40
    cF
    funimass3
    sylancl
    mpbiri
    @45
    @54
    vs
    @51
    @38
    @43
    @51
    wceq
    @44
    @53
    @40
    @43
    @51
    cF
    imaeq2
    sseq1d
    rspcev
    syl2anc
    ex
    jcad
    @33
    @42
    @46
    @41
    @33
    @46
    @42
    @41
    @33
    @45
    @42
    @41
    wi
    vs
    @38
    @33
    @43
    @38
    wcel
    #
    @45
    @42
    @41
    @33
    @67
    @45
    wa
    #
    @42
    wa
    #
    wa
    @2
    @44
    cL
    wcel
    #
    @42
    @45
    @41
    @33
    @2
    @69
    @49
    adantr
    @33
    @67
    @45
    @42
    @70
    @67
    @43
    @36
    wceq
    #
    vx
    cL
    wrex
    #
    @33
    @45
    @42
    @70
    wi
    #
    wi
    #
    @43
    cvv
    wcel
    @67
    @72
    wb
    vs
    vex
    vx
    cL
    @36
    @43
    @37
    cvv
    @63
    elrnmpt
    ax-mp
    @33
    @71
    @74
    vx
    cL
    @33
    @35
    cL
    wcel
    #
    wa
    #
    @74
    @71
    cF
    @36
    cima
    #
    @40
    wss
    #
    @42
    @77
    cL
    wcel
    #
    wi
    #
    wi
    @76
    @78
    @42
    @79
    @76
    @78
    @42
    wa
    #
    wa
    #
    @77
    @35
    @8
    cin
    #
    cL
    @82
    @77
    @83
    @82
    @77
    @35
    wss
    #
    @77
    @8
    wss
    @77
    @83
    wss
    @82
    @84
    @36
    @36
    wss
    #
    @36
    ssid
    @82
    @65
    @36
    @60
    wss
    #
    @84
    @85
    wb
    @4
    @65
    @9
    @75
    @81
    @66
    ad3antrrr
    #
    cF
    @35
    cnvimass
    #
    @36
    @35
    cF
    funimass3
    sylancl
    mpbiri
    cF
    @36
    imassrn
    @77
    @35
    @8
    ssin
    sylanblc
    @82
    vz
    @83
    @77
    vz
    cv
    #
    @83
    wcel
    @89
    @35
    wcel
    #
    @89
    @8
    wcel
    #
    wa
    @82
    @89
    @77
    wcel
    #
    @89
    @35
    @8
    elin
    @82
    @90
    @91
    @92
    @82
    @91
    @90
    @92
    @82
    @91
    vy
    cv
    #
    cF
    cfv
    #
    @89
    wceq
    #
    vy
    cY
    wrex
    #
    @90
    @92
    wi
    #
    @4
    @91
    @96
    wb
    #
    @9
    @75
    @81
    @3
    @0
    @98
    @2
    @3
    @29
    @98
    @30
    vy
    cY
    @89
    cF
    fvelrnb
    syl
    3ad2ant3
    ad3antrrr
    @82
    @95
    @97
    vy
    cY
    @82
    @93
    cY
    wcel
    #
    wa
    #
    @94
    @35
    wcel
    #
    @94
    @77
    wcel
    #
    wi
    @95
    @97
    @100
    @101
    @102
    @100
    @101
    wa
    #
    @65
    @86
    wa
    @93
    @36
    wcel
    #
    @102
    @103
    @65
    @86
    @82
    @65
    @99
    @101
    @87
    ad2antrr
    @88
    jctir
    @100
    @101
    @104
    @100
    @65
    @93
    @60
    wcel
    #
    @101
    @104
    wb
    @76
    @65
    @81
    @99
    @4
    @65
    @9
    @75
    @66
    ad2antrr
    ad2antrr
    @82
    @105
    @99
    @82
    @60
    cY
    @93
    @4
    @60
    cY
    wceq
    #
    @9
    @75
    @81
    @3
    @0
    @106
    @2
    @62
    3ad2ant3
    ad3antrrr
    eleq2d
    biimpar
    @93
    @35
    cF
    fvimacnv
    syl2anc
    biimpa
    @36
    @93
    cF
    funfvima2
    sylc
    ex
    @95
    @101
    @90
    @102
    @92
    @94
    @89
    @35
    eleq1
    @94
    @89
    @77
    eleq1
    imbi12d
    syl5ibcom
    rexlimdva
    sylbid
    com23
    impd
    syl5bi
    ssrdv
    eqssd
    @76
    @83
    cL
    wcel
    #
    @81
    @4
    @9
    @75
    @107
    @2
    @0
    @9
    @75
    @107
    wi
    wi
    @3
    @2
    @75
    @9
    @107
    @2
    @75
    @9
    @107
    @35
    @8
    cL
    cX
    filin
    3exp
    com23
    3ad2ant2
    imp31
    adantr
    eqeltrd
    exp32
    @71
    @45
    @78
    @73
    @80
    @71
    @44
    @77
    @40
    @43
    @36
    cF
    imaeq2
    #
    sseq1d
    @71
    @70
    @79
    @42
    @71
    @44
    @77
    cL
    @108
    eleq1d
    imbi2d
    imbi12d
    syl5ibrcom
    rexlimdva
    syl5bi
    imp44
    @33
    @68
    @42
    simprr
    @33
    @67
    @45
    @42
    simprlr
    @44
    @40
    cL
    cX
    filss
    syl13anc
    exp44
    rexlimdv
    com23
    impd
    impbid
    @33
    @17
    @38
    @13
    wcel
    #
    @3
    @48
    @47
    wb
    @4
    @17
    @9
    @19
    adantr
    vx
    cA
    cF
    cL
    cX
    cY
    rnelfmlem
    #
    @0
    @2
    @3
    @9
    simpl3
    vs
    @40
    @38
    cL
    cF
    cX
    cY
    elfm
    syl3anc
    bitr4d
    eqrdv
    @33
    @15
    @109
    @39
    @6
    wcel
    @4
    @15
    @9
    @20
    adantr
    @110
    @13
    @38
    @5
    fnfvelrn
    syl2anc
    eqeltrd
    ex
    impbid
end
