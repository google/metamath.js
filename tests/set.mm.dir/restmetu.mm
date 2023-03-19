include "c0.mm"
include "wne.mm"
include "cpsmet.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "cxp.mm"
include "crp.mm"
include "cres.mm"
include "ccnv.mm"
include "cc0.mm"
include "cv.mm"
include "cico.mm"
include "co.mm"
include "cima.mm"
include "cmpt.mm"
include "crn.mm"
include "cfg.mm"
include "cpw.mm"
include "cin.mm"
include "crab.mm"
include "cmetu.mm"
include "crest.mm"
include "cfbas.mm"
include "wceq.mm"
include "simp1.mm"
include "psmetres2.mm"
include "3adant1.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "cbvmptv.mm"
include "rneqi.mm"
include "metustfbas.mm"
include "syl2anc.mm"
include "fgval.mm"
include "syl.mm"
include "metuval.mm"
include "cvv.mm"
include "fvex.mm"
include "elfvexd.mm"
include "xpexg.mm"
include "restval.mm"
include "sylancr.mm"
include "wrex.mm"
include "wa.mm"
include "inss2.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "vex.mm"
include "elpw.mm"
include "sylibr.mm"
include "rexlimivw.mm"
include "adantl.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfcri.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfin.mm"
include "nfne.mm"
include "simplr.mm"
include "ineq1.mm"
include "cxr.mm"
include "wf.mm"
include "wfun.mm"
include "simp2.mm"
include "psmetf.mm"
include "ffun.mm"
include "respreima.mm"
include "4syl.mm"
include "ad6antr.mm"
include "eqtr4d.mm"
include "rspe.mm"
include "wb.mm"
include "inex1.mm"
include "eqid.mm"
include "elrnmpt.mm"
include "ax-mp.mm"
include "simpllr.mm"
include "ssinss1.mm"
include "a1i.mm"
include "pweq.mm"
include "eleq2d.mm"
include "syl6bb.mm"
include "ssin.mm"
include "syl6bbr.mm"
include "ad5antlr.mm"
include "mpbir2and.mm"
include "inelcm.mm"
include "sylib.mm"
include "r19.29af2.mm"
include "ssn0.mm"
include "ancoms.mm"
include "3adant2.mm"
include "metuel.mm"
include "simplbda.mm"
include "adantr.mm"
include "r19.29a.mm"
include "r19.29an.mm"
include "jca.mm"
include "cdif.mm"
include "cun.mm"
include "simprl.mm"
include "elpwid.mm"
include "simpl3.mm"
include "xpss12.mm"
include "sstrd.mm"
include "difssd.mm"
include "unssd.mm"
include "eqidd.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "ad4antr.mm"
include "cnvexg.mm"
include "imaexg.mm"
include "mpbird.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "ssdif0.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "simpr.mm"
include "eqsstr3d.mm"
include "ssundif.mm"
include "difcom.mm"
include "difdif2.mm"
include "sseq1i.mm"
include "3bitri.mm"
include "wex.mm"
include "elin.mm"
include "anbi1i.mm"
include "ancom.mm"
include "exbii.mm"
include "n0.mm"
include "df-rex.mm"
include "3bitr4i.mm"
include "biimpi.mm"
include "ad2antll.mm"
include "r19.29vva.mm"
include "indir.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtr3i.mm"
include "uneq2i.mm"
include "un0.mm"
include "3eqtri.mm"
include "df-ss.mm"
include "syl5req.mm"
include "impbida.mm"
include "ineq2d.mm"
include "neeq1d.mm"
include "elrab.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"

theorem restmetu
  let cA: class A
  let cD: class D
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w


  assert |- ( ( A =/= (/) /\ D e. ( PsMet ` X ) /\ A C_ X ) -> ( ( metUnif ` D ) |`t ( A X. A ) ) = ( metUnif ` ( D |` ( A X. A ) ) ) )

  proof
    cA
    c0
    wne
    #
    cD
    cX
    cpsmet
    cfv
    #
    wcel
    #
    cA
    cX
    wss
    #
    w3a
    #
    cA
    cA
    cxp
    #
    va
    crp
    cD
    @5
    cres
    #
    ccnv
    #
    cc0
    va
    cv
    #
    cico
    co
    #
    cima
    #
    cmpt
    #
    crn
    #
    cfg
    co
    #
    @12
    vv
    cv
    #
    cpw
    #
    cin
    #
    c0
    wne
    #
    vv
    @5
    cpw
    #
    crab
    #
    @6
    cmetu
    cfv
    #
    cD
    cmetu
    cfv
    #
    @5
    crest
    co
    #
    @4
    @12
    @5
    cfbas
    cfv
    wcel
    #
    @13
    @19
    wceq
    @4
    @0
    @6
    cA
    cpsmet
    cfv
    wcel
    #
    @23
    @0
    @2
    @3
    simp1
    @2
    @3
    @24
    @0
    cD
    cA
    cX
    psmetres2
    3adant1
    #
    @6
    @12
    cA
    vb
    @11
    vb
    crp
    @7
    cc0
    vb
    cv
    #
    cico
    co
    #
    cima
    #
    cmpt
    va
    vb
    crp
    @10
    @28
    @8
    @26
    wceq
    #
    @9
    @27
    @7
    @8
    @26
    cc0
    cico
    oveq2
    #
    imaeq2d
    cbvmptv
    #
    rneqi
    metustfbas
    syl2anc
    vv
    @12
    @5
    fgval
    syl
    @4
    @24
    @20
    @13
    wceq
    @25
    @6
    cA
    va
    metuval
    syl
    @4
    @22
    vv
    @21
    @14
    @5
    cin
    #
    cmpt
    #
    crn
    #
    @19
    @4
    @21
    cvv
    wcel
    @5
    cvv
    wcel
    #
    @22
    @34
    wceq
    cD
    cmetu
    fvex
    @4
    cA
    cvv
    wcel
    #
    @36
    @35
    @4
    @6
    cpsmet
    cA
    @25
    elfvexd
    #
    @37
    cA
    cA
    cvv
    cvv
    xpexg
    syl2anc
    vv
    @5
    @21
    cvv
    cvv
    restval
    sylancr
    @4
    vu
    @34
    @19
    @4
    vu
    cv
    #
    @32
    wceq
    #
    vv
    @21
    wrex
    #
    @38
    @18
    wcel
    #
    @12
    @38
    cpw
    #
    cin
    #
    c0
    wne
    #
    wa
    #
    @38
    @34
    wcel
    #
    @38
    @19
    wcel
    @4
    @40
    @45
    @4
    @40
    wa
    @41
    @44
    @40
    @41
    @4
    @39
    @41
    vv
    @21
    @39
    @38
    @5
    wss
    #
    @41
    @39
    @47
    @32
    @5
    wss
    @14
    @5
    inss2
    @38
    @32
    @5
    sseq1
    mpbiri
    @38
    @5
    vu
    vex
    #
    elpw
    sylibr
    rexlimivw
    adantl
    @4
    @39
    @44
    vv
    @21
    @4
    @14
    @21
    wcel
    #
    wa
    #
    @39
    wa
    #
    vw
    cv
    #
    @14
    wss
    #
    @44
    vw
    va
    crp
    cD
    ccnv
    #
    @9
    cima
    #
    cmpt
    #
    crn
    #
    @51
    @52
    @57
    wcel
    #
    wa
    #
    @53
    wa
    #
    @52
    @55
    wceq
    #
    @44
    va
    crp
    @59
    @53
    va
    @51
    @58
    va
    @51
    va
    nfv
    va
    vw
    @57
    va
    @56
    va
    crp
    @55
    nfmpt1
    nfrn
    nfcri
    nfan
    @53
    va
    nfv
    nfan
    va
    @43
    c0
    va
    @12
    @42
    va
    @11
    va
    crp
    @10
    nfmpt1
    nfrn
    va
    @42
    nfcv
    nfin
    va
    c0
    nfcv
    nfne
    @60
    @8
    crp
    wcel
    #
    wa
    #
    @61
    wa
    #
    @52
    @5
    cin
    #
    @12
    wcel
    #
    @65
    @42
    wcel
    #
    @44
    @64
    @65
    @10
    wceq
    #
    va
    crp
    wrex
    #
    @66
    @64
    @62
    @68
    @69
    @60
    @62
    @61
    simplr
    @64
    @65
    @55
    @5
    cin
    #
    @10
    @61
    @65
    @70
    wceq
    @63
    @52
    @55
    @5
    ineq1
    adantl
    @4
    @10
    @70
    wceq
    #
    @49
    @39
    @58
    @53
    @62
    @61
    @4
    @2
    cX
    cX
    cxp
    #
    cxr
    cD
    wf
    #
    cD
    wfun
    #
    @71
    @0
    @2
    @3
    simp2
    #
    cD
    cX
    psmetf
    #
    @72
    cxr
    cD
    ffun
    #
    @9
    @5
    cD
    respreima
    4syl
    ad6antr
    eqtr4d
    @68
    va
    crp
    rspe
    syl2anc
    @65
    cvv
    wcel
    @66
    @69
    wb
    @52
    @5
    vw
    vex
    #
    inex1
    #
    va
    crp
    @10
    @65
    @11
    cvv
    @11
    eqid
    elrnmpt
    ax-mp
    sylibr
    @64
    @67
    @65
    @14
    wss
    #
    @65
    @5
    wss
    #
    @64
    @53
    @80
    @59
    @53
    @62
    @61
    simpllr
    @52
    @5
    @14
    ssinss1
    syl
    @81
    @64
    @52
    @5
    inss2
    a1i
    @39
    @67
    @80
    @81
    wa
    #
    wb
    @50
    @58
    @53
    @62
    @61
    @39
    @67
    @65
    @32
    wss
    #
    @82
    @39
    @67
    @65
    @32
    cpw
    #
    wcel
    @83
    @39
    @42
    @84
    @65
    @38
    @32
    pweq
    eleq2d
    @65
    @32
    @79
    elpw
    syl6bb
    @65
    @14
    @5
    ssin
    syl6bbr
    ad5antlr
    mpbir2and
    @65
    @12
    @42
    inelcm
    syl2anc
    @60
    @58
    @61
    va
    crp
    wrex
    #
    @51
    @58
    @53
    simplr
    @52
    cvv
    wcel
    @58
    @85
    wb
    @78
    va
    crp
    @55
    @52
    @56
    cvv
    @56
    eqid
    #
    elrnmpt
    ax-mp
    sylib
    r19.29af2
    @50
    @53
    vw
    @57
    wrex
    #
    @39
    @4
    @49
    @14
    @72
    wss
    #
    @87
    @4
    cX
    c0
    wne
    #
    @2
    @49
    @88
    @87
    wa
    wb
    @0
    @3
    @89
    @2
    @3
    @0
    @89
    cA
    cX
    ssn0
    ancoms
    3adant2
    #
    @75
    vw
    cD
    @14
    cX
    va
    metuel
    syl2anc
    simplbda
    adantr
    r19.29a
    r19.29an
    jca
    @4
    @45
    wa
    #
    @38
    @72
    @5
    cdif
    #
    cun
    #
    @21
    wcel
    #
    @38
    @93
    @5
    cin
    #
    wceq
    #
    @40
    @91
    @94
    @93
    @72
    wss
    #
    @52
    @93
    wss
    #
    vw
    @57
    wrex
    #
    @91
    @38
    @92
    @72
    @91
    @38
    @5
    @72
    @91
    @38
    @5
    @4
    @41
    @44
    simprl
    elpwid
    #
    @91
    @3
    @3
    @5
    @72
    wss
    @0
    @2
    @3
    @45
    simpl3
    #
    @101
    cA
    cX
    cA
    cX
    xpss12
    syl2anc
    sstrd
    @91
    @72
    @5
    difssd
    unssd
    @91
    @14
    @28
    wceq
    #
    @99
    vv
    vb
    @42
    crp
    @91
    @14
    @42
    wcel
    #
    wa
    #
    @26
    crp
    wcel
    #
    wa
    #
    @102
    wa
    #
    @54
    @27
    cima
    #
    @57
    wcel
    #
    @108
    @93
    wss
    #
    @99
    @107
    @109
    @108
    @55
    wceq
    #
    va
    crp
    wrex
    #
    @107
    @105
    @108
    @108
    wceq
    #
    @112
    @104
    @105
    @102
    simplr
    @107
    @108
    eqidd
    @111
    @113
    va
    @26
    crp
    @29
    @55
    @108
    @108
    @29
    @9
    @27
    @54
    @30
    imaeq2d
    eqeq2d
    rspcev
    syl2anc
    @107
    @2
    @54
    cvv
    wcel
    @108
    cvv
    wcel
    @109
    @112
    wb
    @4
    @2
    @45
    @103
    @105
    @102
    @75
    ad4antr
    #
    cD
    @1
    cnvexg
    @54
    @27
    cvv
    imaexg
    va
    crp
    @55
    @108
    @56
    cvv
    @86
    elrnmpt
    4syl
    mpbird
    @107
    @108
    @72
    cdif
    #
    @108
    @5
    cin
    #
    cun
    #
    @38
    wss
    #
    @110
    @107
    @115
    @116
    @38
    @107
    @115
    c0
    @38
    @107
    @108
    @72
    wss
    #
    @115
    c0
    wceq
    @107
    @2
    @119
    @114
    @2
    cD
    cdm
    #
    @108
    @72
    cD
    @27
    cnvimass
    @2
    @73
    @120
    @72
    wceq
    @76
    @72
    cxr
    cD
    fdm
    syl
    syl5sseq
    syl
    @108
    @72
    ssdif0
    sylib
    @38
    0ss
    syl6eqss
    @107
    @116
    @28
    @38
    @107
    @2
    @73
    @74
    @28
    @116
    wceq
    @114
    @76
    @77
    @27
    @5
    cD
    respreima
    4syl
    @107
    @28
    @14
    @38
    @106
    @102
    simpr
    @107
    @14
    @38
    @91
    @103
    @105
    @102
    simpllr
    elpwid
    eqsstr3d
    eqsstr3d
    unssd
    @110
    @108
    @38
    cdif
    @92
    wss
    @108
    @92
    cdif
    #
    @38
    wss
    @118
    @108
    @38
    @92
    ssundif
    @108
    @38
    @92
    difcom
    @121
    @117
    @38
    @108
    @72
    @5
    difdif2
    sseq1i
    3bitri
    sylibr
    @98
    @110
    vw
    @108
    @57
    @52
    @108
    @93
    sseq1
    rspcev
    syl2anc
    @44
    @102
    vb
    crp
    wrex
    #
    vv
    @42
    wrex
    #
    @4
    @41
    @44
    @123
    @14
    @43
    wcel
    #
    vv
    wex
    @103
    @122
    wa
    #
    vv
    wex
    @44
    @123
    @124
    @125
    vv
    @124
    @14
    @12
    wcel
    #
    @103
    wa
    @122
    @103
    wa
    @125
    @14
    @12
    @42
    elin
    @126
    @122
    @103
    @14
    cvv
    wcel
    @126
    @122
    wb
    vv
    vex
    vb
    crp
    @28
    @14
    @11
    cvv
    @31
    elrnmpt
    ax-mp
    anbi1i
    @122
    @103
    ancom
    3bitri
    exbii
    vv
    @43
    n0
    @122
    vv
    @42
    df-rex
    3bitr4i
    biimpi
    ad2antll
    r19.29vva
    @91
    @89
    @2
    @94
    @97
    @99
    wa
    wb
    @4
    @89
    @45
    @90
    adantr
    @4
    @2
    @45
    @75
    adantr
    vw
    cD
    @93
    cX
    va
    metuel
    syl2anc
    mpbir2and
    @91
    @95
    @38
    @5
    cin
    #
    @38
    @95
    @127
    @92
    @5
    cin
    #
    cun
    @127
    c0
    cun
    @127
    @38
    @92
    @5
    indir
    @128
    c0
    @127
    @5
    @92
    cin
    @128
    c0
    @5
    @92
    incom
    @5
    @72
    disjdif
    eqtr3i
    uneq2i
    @127
    un0
    3eqtri
    @91
    @47
    @127
    @38
    wceq
    @100
    @38
    @5
    df-ss
    sylib
    syl5req
    @39
    @96
    vv
    @93
    @21
    @14
    @93
    wceq
    @32
    @95
    @38
    @14
    @93
    @5
    ineq1
    eqeq2d
    rspcev
    syl2anc
    impbida
    @38
    cvv
    wcel
    @46
    @40
    wb
    @48
    vv
    @21
    @32
    @38
    @33
    cvv
    @33
    eqid
    elrnmpt
    ax-mp
    @17
    @44
    vv
    @38
    @18
    @14
    @38
    wceq
    #
    @16
    @43
    c0
    @129
    @15
    @42
    @12
    @14
    @38
    pweq
    ineq2d
    neeq1d
    elrab
    3bitr4g
    eqrdv
    eqtrd
    3eqtr4rd
end
