include "cvv.mm"
include "wcel.mm"
include "wf1.mm"
include "cres.mm"
include "cid.mm"
include "wceq.mm"
include "w3a.mm"
include "cv.mm"
include "cz.mm"
include "cmap.mm"
include "co.mm"
include "ccom.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc0.mm"
include "wa.mm"
include "cn0.mm"
include "wrex.mm"
include "wf.mm"
include "simpr.mm"
include "wb.mm"
include "nn0ex.mm"
include "simp1.mm"
include "adantr.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simp2.mm"
include "f1f.mm"
include "syl.mm"
include "ad2antrr.mm"
include "fco.mm"
include "syl2anc.mm"
include "f1dmex.mm"
include "mpbird.mm"
include "simprl.mm"
include "resco.mm"
include "simpll3.mm"
include "coeq2d.mm"
include "coires1.mm"
include "syl6eq.mm"
include "syl5eq.mm"
include "eqtr4d.mm"
include "wss.mm"
include "simpll1.mm"
include "oveq2.mm"
include "sseq12d.mm"
include "zex.mm"
include "nn0ssz.mm"
include "mapss.mm"
include "mp2an.mm"
include "vtoclg.mm"
include "simplr.mm"
include "sseldd.mm"
include "coeq1.mm"
include "fveq2d.mm"
include "eqid.mm"
include "fvex.mm"
include "fvmpt.mm"
include "simprr.mm"
include "eqtr3d.mm"
include "reseq1.mm"
include "eqeq2d.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "ex.mm"
include "rexlimdva.mm"
include "ccnv.mm"
include "crn.mm"
include "cdif.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "cin.mm"
include "c0.mm"
include "wf1o.mm"
include "f1cnv.mm"
include "f1of.mm"
include "3syl.mm"
include "c0ex.mm"
include "fconst.mm"
include "a1i.mm"
include "disjdif.mm"
include "fun.mm"
include "syl21anc.mm"
include "frn.mm"
include "undif.mm"
include "sylib.mm"
include "0nn0.mm"
include "snssi.mm"
include "ax-mp.mm"
include "ssequn2.mm"
include "mpbi.mm"
include "feq23d.mm"
include "resundir.mm"
include "cnvresid.mm"
include "cima.mm"
include "wfun.mm"
include "simpl2.mm"
include "df-f1.mm"
include "simprbi.mm"
include "funcnvres.mm"
include "simpl3.mm"
include "cnveqd.mm"
include "df-ima.mm"
include "rneqd.mm"
include "rnresi.mm"
include "reseq2d.mm"
include "3eqtr3d.mm"
include "syl5reqr.mm"
include "cdm.mm"
include "dmres.mm"
include "wne.mm"
include "snnz.mm"
include "dmxp.mm"
include "ineq2i.mm"
include "inss1.mm"
include "syl6req.mm"
include "resss.mm"
include "rnss.mm"
include "mp1i.mm"
include "eqsstrd.mm"
include "syl5ss.mm"
include "inssdif0.mm"
include "wrel.mm"
include "relres.mm"
include "reldm0.mm"
include "sylibr.mm"
include "uneq12d.mm"
include "un0.mm"
include "eqtrd.mm"
include "fss.mm"
include "sylancl.mm"
include "0z.mm"
include "coundir.mm"
include "coass.mm"
include "f1cocnv1.mm"
include "ineq1i.mm"
include "incom.mm"
include "3eqtri.mm"
include "coeq0.mm"
include "mpbir.mm"
include "fcoi1.mm"
include "3eqtrd.mm"
include "impbid.mm"
include "abbidv.mm"

theorem diophrw
  let cP: class P
  let cS: class S
  let cT: class T
  let cM: class M
  let cO: class O
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d

  disjoint S a
  disjoint S b
  disjoint S c
  disjoint S d
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint T a
  disjoint T b
  disjoint T c
  disjoint T d
  disjoint M a
  disjoint M b
  disjoint M c
  disjoint M d
  disjoint O a
  disjoint O b
  disjoint O c
  disjoint O d
  disjoint P b
  disjoint P c
  disjoint P d
  assert |- ( ( S e. _V /\ M : T -1-1-> S /\ ( M |` O ) = ( _I |` O ) ) -> { a | E. b e. ( NN0 ^m S ) ( a = ( b |` O ) /\ ( ( d e. ( ZZ ^m S ) |-> ( P ` ( d o. M ) ) ) ` b ) = 0 ) } = { a | E. c e. ( NN0 ^m T ) ( a = ( c |` O ) /\ ( P ` c ) = 0 ) } )

  proof
    cS
    cvv
    wcel
    #
    cT
    cS
    cM
    wf1
    #
    cM
    cO
    cres
    #
    cid
    cO
    cres
    #
    wceq
    #
    w3a
    #
    va
    cv
    #
    vb
    cv
    #
    cO
    cres
    #
    wceq
    #
    @7
    vd
    cz
    cS
    cmap
    co
    #
    vd
    cv
    #
    cM
    ccom
    #
    cP
    cfv
    #
    cmpt
    #
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vb
    cn0
    cS
    cmap
    co
    #
    wrex
    #
    @6
    vc
    cv
    #
    cO
    cres
    #
    wceq
    #
    @20
    cP
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vc
    cn0
    cT
    cmap
    co
    #
    wrex
    #
    va
    @5
    @19
    @27
    @5
    @17
    @27
    vb
    @18
    @5
    @7
    @18
    wcel
    #
    wa
    #
    @17
    @27
    @29
    @17
    wa
    #
    @7
    cM
    ccom
    #
    @26
    wcel
    #
    @6
    @31
    cO
    cres
    #
    wceq
    #
    @31
    cP
    cfv
    #
    cc0
    wceq
    #
    @27
    @30
    @32
    cT
    cn0
    @31
    wf
    #
    @30
    cS
    cn0
    @7
    wf
    #
    cT
    cS
    cM
    wf
    #
    @37
    @29
    @38
    @17
    @29
    @28
    @38
    @5
    @28
    simpr
    @29
    cn0
    cvv
    wcel
    #
    @0
    @28
    @38
    wb
    nn0ex
    @5
    @0
    @28
    @0
    @1
    @4
    simp1
    #
    adantr
    cn0
    cS
    @7
    cvv
    cvv
    elmapg
    sylancr
    mpbid
    adantr
    @5
    @39
    @28
    @17
    @5
    @1
    @39
    @0
    @1
    @4
    simp2
    #
    cT
    cS
    cM
    f1f
    #
    syl
    ad2antrr
    cT
    cS
    cn0
    @7
    cM
    fco
    syl2anc
    @30
    @40
    cT
    cvv
    wcel
    #
    @32
    @37
    wb
    nn0ex
    @5
    @44
    @28
    @17
    @5
    @1
    @0
    @44
    @42
    @41
    cT
    cS
    cvv
    cM
    f1dmex
    syl2anc
    #
    ad2antrr
    cn0
    cT
    @31
    cvv
    cvv
    elmapg
    sylancr
    mpbird
    @30
    @6
    @8
    @33
    @29
    @9
    @16
    simprl
    @30
    @33
    @7
    @2
    ccom
    #
    @8
    @7
    cM
    cO
    resco
    @30
    @46
    @7
    @3
    ccom
    @8
    @30
    @2
    @3
    @7
    @0
    @1
    @4
    @28
    @17
    simpll3
    coeq2d
    @7
    cO
    coires1
    syl6eq
    syl5eq
    eqtr4d
    @30
    @15
    @35
    cc0
    @30
    @7
    @10
    wcel
    @15
    @35
    wceq
    @30
    @18
    @10
    @7
    @30
    @0
    @18
    @10
    wss
    #
    @0
    @1
    @4
    @28
    @17
    simpll1
    cn0
    @6
    cmap
    co
    #
    cz
    @6
    cmap
    co
    #
    wss
    #
    @47
    va
    cS
    cvv
    @6
    cS
    wceq
    @48
    @18
    @49
    @10
    @6
    cS
    cn0
    cmap
    oveq2
    @6
    cS
    cz
    cmap
    oveq2
    sseq12d
    cz
    cvv
    wcel
    #
    cn0
    cz
    wss
    #
    @50
    zex
    nn0ssz
    cn0
    cz
    @6
    cvv
    mapss
    mp2an
    vtoclg
    syl
    @5
    @28
    @17
    simplr
    sseldd
    vd
    @7
    @13
    @35
    @10
    @14
    @11
    @7
    wceq
    @12
    @31
    cP
    @11
    @7
    cM
    coeq1
    fveq2d
    @14
    eqid
    #
    @31
    cP
    fvex
    fvmpt
    syl
    @29
    @9
    @16
    simprr
    eqtr3d
    @25
    @34
    @36
    wa
    vc
    @31
    @26
    @20
    @31
    wceq
    #
    @22
    @34
    @24
    @36
    @54
    @21
    @33
    @6
    @20
    @31
    cO
    reseq1
    eqeq2d
    @54
    @23
    @35
    cc0
    @20
    @31
    cP
    fveq2
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    ex
    rexlimdva
    @5
    @25
    @19
    vc
    @26
    @5
    @20
    @26
    wcel
    #
    wa
    #
    @25
    @19
    @56
    @25
    wa
    #
    @20
    cM
    ccnv
    #
    ccom
    #
    cS
    cM
    crn
    #
    cdif
    #
    cc0
    csn
    #
    cxp
    #
    cun
    #
    @18
    wcel
    #
    @6
    @64
    cO
    cres
    #
    wceq
    #
    @64
    @14
    cfv
    #
    cc0
    wceq
    #
    @19
    @57
    @65
    cS
    cn0
    @64
    wf
    #
    @57
    @60
    @61
    cun
    #
    cn0
    @62
    cun
    #
    @64
    wf
    #
    @70
    @57
    @60
    cn0
    @59
    wf
    #
    @61
    @62
    @63
    wf
    #
    @60
    @61
    cin
    #
    c0
    wceq
    #
    @73
    @57
    cT
    cn0
    @20
    wf
    #
    @60
    cT
    @58
    wf
    #
    @74
    @56
    @78
    @25
    @56
    @55
    @78
    @5
    @55
    simpr
    @56
    @40
    @44
    @55
    @78
    wb
    nn0ex
    @5
    @44
    @55
    @45
    adantr
    cn0
    cT
    @20
    cvv
    cvv
    elmapg
    sylancr
    mpbid
    #
    adantr
    #
    @57
    @1
    @60
    cT
    @58
    wf1o
    @79
    @5
    @1
    @55
    @25
    @42
    ad2antrr
    #
    cT
    cS
    cM
    f1cnv
    @60
    cT
    @58
    f1of
    3syl
    #
    @60
    cT
    cn0
    @20
    @58
    fco
    syl2anc
    @75
    @57
    @61
    cc0
    c0ex
    fconst
    a1i
    #
    @77
    @57
    @60
    cS
    disjdif
    #
    a1i
    #
    @60
    @61
    cn0
    @62
    @59
    @63
    fun
    syl21anc
    @57
    @71
    @72
    cS
    cn0
    @64
    @57
    @60
    cS
    wss
    #
    @71
    cS
    wceq
    @5
    @87
    @55
    @25
    @5
    @1
    @39
    @87
    @42
    @43
    cT
    cS
    cM
    frn
    3syl
    ad2antrr
    @60
    cS
    undif
    sylib
    #
    @72
    cn0
    wceq
    #
    @57
    @62
    cn0
    wss
    #
    @89
    cc0
    cn0
    wcel
    @90
    0nn0
    cc0
    cn0
    snssi
    ax-mp
    @62
    cn0
    ssequn2
    mpbi
    a1i
    feq23d
    mpbid
    @5
    @65
    @70
    wb
    #
    @55
    @25
    @5
    @40
    @0
    @91
    nn0ex
    @41
    cn0
    cS
    @64
    cvv
    cvv
    elmapg
    sylancr
    ad2antrr
    mpbird
    @57
    @6
    @21
    @66
    @56
    @22
    @24
    simprl
    @56
    @21
    @66
    wceq
    @25
    @56
    @66
    @21
    c0
    cun
    #
    @21
    @56
    @66
    @59
    cO
    cres
    #
    @63
    cO
    cres
    #
    cun
    @92
    @59
    @63
    cO
    resundir
    @56
    @93
    @21
    @94
    c0
    @56
    @93
    @20
    @58
    cO
    cres
    #
    ccom
    #
    @21
    @20
    @58
    cO
    resco
    @56
    @96
    @20
    @3
    ccom
    @21
    @56
    @95
    @3
    @20
    @56
    @3
    @3
    ccnv
    #
    @95
    cO
    cnvresid
    @56
    @2
    ccnv
    #
    @58
    cM
    cO
    cima
    #
    cres
    #
    @97
    @95
    @56
    @1
    @58
    wfun
    #
    @98
    @100
    wceq
    @0
    @1
    @4
    @55
    simpl2
    @1
    @39
    @101
    cT
    cS
    cM
    df-f1
    simprbi
    cO
    cM
    funcnvres
    3syl
    @56
    @2
    @3
    @0
    @1
    @4
    @55
    simpl3
    #
    cnveqd
    @56
    @99
    cO
    @58
    @56
    @99
    @2
    crn
    #
    cO
    cM
    cO
    df-ima
    @56
    @103
    @3
    crn
    #
    cO
    @56
    @2
    @3
    @102
    rneqd
    #
    cO
    rnresi
    #
    syl6eq
    syl5eq
    reseq2d
    3eqtr3d
    syl5reqr
    coeq2d
    @20
    cO
    coires1
    syl6eq
    syl5eq
    @56
    @94
    cdm
    #
    c0
    wceq
    #
    @94
    c0
    wceq
    #
    @56
    @107
    cO
    @63
    cdm
    #
    cin
    #
    c0
    @63
    cO
    dmres
    @56
    @111
    cO
    @61
    cin
    #
    c0
    @110
    @61
    cO
    @62
    c0
    wne
    @110
    @61
    wceq
    cc0
    c0ex
    snnz
    @61
    @62
    dmxp
    ax-mp
    #
    ineq2i
    @56
    cO
    cS
    cin
    #
    @60
    wss
    @112
    c0
    wceq
    @56
    @114
    cO
    @60
    cO
    cS
    inss1
    @56
    cO
    @103
    @60
    @56
    @103
    @104
    cO
    @105
    @106
    syl6req
    @2
    cM
    wss
    @103
    @60
    wss
    @56
    cM
    cO
    resss
    @2
    cM
    rnss
    mp1i
    eqsstrd
    syl5ss
    cO
    cS
    @60
    inssdif0
    sylib
    syl5eq
    syl5eq
    @94
    wrel
    @109
    @108
    wb
    @63
    cO
    relres
    @94
    reldm0
    ax-mp
    sylibr
    uneq12d
    syl5eq
    @21
    un0
    syl6req
    adantr
    eqtrd
    @57
    @68
    @64
    cM
    ccom
    #
    cP
    cfv
    #
    @23
    cc0
    @57
    @64
    @10
    wcel
    #
    @68
    @116
    wceq
    @57
    @117
    cS
    cz
    @64
    wf
    #
    @57
    @71
    cz
    @62
    cun
    #
    @64
    wf
    #
    @118
    @57
    @60
    cz
    @59
    wf
    #
    @75
    @77
    @120
    @57
    cT
    cz
    @20
    wf
    #
    @79
    @121
    @56
    @122
    @25
    @56
    @78
    @52
    @122
    @80
    nn0ssz
    cT
    cn0
    cz
    @20
    fss
    sylancl
    adantr
    @83
    @60
    cT
    cz
    @20
    @58
    fco
    syl2anc
    @84
    @86
    @60
    @61
    cz
    @62
    @59
    @63
    fun
    syl21anc
    @57
    @71
    @119
    cS
    cz
    @64
    @88
    @119
    cz
    wceq
    #
    @57
    @62
    cz
    wss
    #
    @123
    cc0
    cz
    wcel
    @124
    0z
    cc0
    cz
    snssi
    ax-mp
    @62
    cz
    ssequn2
    mpbi
    a1i
    feq23d
    mpbid
    @5
    @117
    @118
    wb
    #
    @55
    @25
    @5
    @51
    @0
    @125
    zex
    @41
    cz
    cS
    @64
    cvv
    cvv
    elmapg
    sylancr
    ad2antrr
    mpbird
    vd
    @64
    @13
    @116
    @10
    @14
    @11
    @64
    wceq
    @12
    @115
    cP
    @11
    @64
    cM
    coeq1
    fveq2d
    @53
    @115
    cP
    fvex
    fvmpt
    syl
    @57
    @115
    @20
    cP
    @57
    @115
    @59
    cM
    ccom
    #
    @63
    cM
    ccom
    #
    cun
    #
    @20
    @59
    @63
    cM
    coundir
    @57
    @128
    @20
    cid
    cT
    cres
    #
    ccom
    #
    c0
    cun
    #
    @20
    @57
    @126
    @130
    @127
    c0
    @57
    @126
    @20
    @58
    cM
    ccom
    #
    ccom
    #
    @130
    @20
    @58
    cM
    coass
    @57
    @1
    @133
    @130
    wceq
    @82
    @1
    @132
    @129
    @20
    cT
    cS
    cM
    f1cocnv1
    coeq2d
    syl
    syl5eq
    @127
    c0
    wceq
    #
    @57
    @134
    @110
    @60
    cin
    #
    c0
    wceq
    @135
    @61
    @60
    cin
    @76
    c0
    @110
    @61
    @60
    @113
    ineq1i
    @61
    @60
    incom
    @85
    3eqtri
    @63
    cM
    coeq0
    mpbir
    a1i
    uneq12d
    @57
    @131
    @130
    @20
    @130
    un0
    @57
    @78
    @130
    @20
    wceq
    @81
    cT
    cn0
    @20
    fcoi1
    syl
    syl5eq
    eqtrd
    syl5eq
    fveq2d
    @56
    @22
    @24
    simprr
    3eqtrd
    @17
    @67
    @69
    wa
    vb
    @64
    @18
    @7
    @64
    wceq
    #
    @9
    @67
    @16
    @69
    @136
    @8
    @66
    @6
    @7
    @64
    cO
    reseq1
    eqeq2d
    @136
    @15
    @68
    cc0
    @7
    @64
    @14
    fveq2
    eqeq1d
    anbi12d
    rspcev
    syl12anc
    ex
    rexlimdva
    impbid
    abbidv
end
