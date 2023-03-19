include "c1stc.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "cn.mm"
include "wf.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "w3a.mm"
include "wex.mm"
include "cpw.mm"
include "1stcclb.mm"
include "crab.mm"
include "wfo.mm"
include "c0.mm"
include "csdm.mm"
include "wne.mm"
include "ctop.mm"
include "1stctop.mm"
include "ad2antrr.mm"
include "topopn.mm"
include "syl.mm"
include "simprrr.mm"
include "simplr.mm"
include "wceq.mm"
include "eleq2.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "simpl.mm"
include "reximi.mm"
include "cbvrexv.mm"
include "sylib.mm"
include "rabn0.mm"
include "sylibr.mm"
include "vex.mm"
include "rabex.mm"
include "0sdom.mm"
include "cvv.mm"
include "ssrab2.mm"
include "ssdomg.mm"
include "mp2.mm"
include "cen.mm"
include "simprrl.mm"
include "nnenom.mm"
include "ensymi.mm"
include "domentr.mm"
include "sylancl.mm"
include "domtr.mm"
include "sylancr.mm"
include "fodomr.mm"
include "syl2anc.mm"
include "cfz.mm"
include "cima.mm"
include "cint.mm"
include "cmpt.mm"
include "cfn.mm"
include "ad3antrrr.mm"
include "crn.mm"
include "imassrn.mm"
include "forn.mm"
include "ad2antll.mm"
include "simprll.mm"
include "elpwid.mm"
include "syl5ss.mm"
include "eqsstrd.mm"
include "adantr.mm"
include "cdm.mm"
include "cin.mm"
include "elfznn.mm"
include "ssriv.mm"
include "fof.mm"
include "fdm.mm"
include "syl5sseqr.mm"
include "sseqin2.mm"
include "elfz1end.mm"
include "ne0i.mm"
include "adantl.mm"
include "sylan2b.mm"
include "eqnetrd.mm"
include "imadisj.mm"
include "necon3bii.mm"
include "cres.mm"
include "fzfid.mm"
include "wfun.mm"
include "ffun.mm"
include "fores.mm"
include "fofi.mm"
include "fiinopn.mm"
include "imp.mm"
include "syl13anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "syl5sseq.mm"
include "id.mm"
include "rgenw.mm"
include "ralrab.mm"
include "mpbir.mm"
include "ssralv.mm"
include "mpisyl.mm"
include "wb.mm"
include "elintg.mm"
include "ad3antlr.mm"
include "mpbird.mm"
include "simpr.mm"
include "ralrimiva.mm"
include "weq.mm"
include "oveq2.mm"
include "imaeq2d.mm"
include "inteqd.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "fvmptg.mm"
include "eleqtrrd.mm"
include "fzssp1.mm"
include "imass2.mm"
include "mp1i.mm"
include "intss.mm"
include "peano2nn.mm"
include "syl2an.mm"
include "3sstr4d.mm"
include "jca.mm"
include "simprlr.mm"
include "rexrab.mm"
include "rexeqdv.mm"
include "wfn.mm"
include "fofn.mm"
include "sseq1.mm"
include "rexrn.mm"
include "bitr3d.mm"
include "funfvima2.mm"
include "intss1.mm"
include "sstr2.mm"
include "3syl.mm"
include "reximdva.mm"
include "sylbid.mm"
include "syl5bir.mm"
include "syld.mm"
include "sseq1d.mm"
include "rexbidva.mm"
include "sylibrd.mm"
include "nnex.mm"
include "mptex.mm"
include "feq1.mm"
include "fveq1.mm"
include "eleq2d.mm"
include "sseq12d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "imbi2d.mm"
include "3anbi123d.mm"
include "spcev.mm"
include "syl3anc.mm"
include "expr.mm"
include "adantrrl.mm"
include "exlimdv.mm"
include "mpd.mm"
include "rexlimddv.mm"

theorem 1stcfb
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vk: setvar k
  let cJ: class J
  let cX: class X
  let va: setvar a
  let vg: setvar g
  let vn: setvar n
  let vw: setvar w
  let vx: setvar x
  let vz: setvar z
  assume 1stcclb.1: |- X = U. J

  disjoint f k
  disjoint f y
  disjoint A f
  disjoint k y
  disjoint A k
  disjoint A y
  disjoint J f
  disjoint J k
  disjoint J y
  disjoint X k
  disjoint X y
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a n
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint f g
  disjoint f n
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint g k
  disjoint g n
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k n
  disjoint k w
  disjoint k x
  disjoint k z
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A z
  disjoint J g
  disjoint J n
  disjoint J w
  disjoint J x
  disjoint J z
  disjoint X g
  disjoint X n
  disjoint X w
  disjoint X x
  disjoint X z
  assert |- ( ( J e. 1stc /\ A e. X ) -> E. f ( f : NN --> J /\ A. k e. NN ( A e. ( f ` k ) /\ ( f ` ( k + 1 ) ) C_ ( f ` k ) ) /\ A. y e. J ( A e. y -> E. k e. NN ( f ` k ) C_ y ) ) )

  proof
    cJ
    c1stc
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    vx
    cv
    #
    com
    cdom
    wbr
    #
    cA
    vz
    cv
    #
    wcel
    #
    cA
    vw
    cv
    #
    wcel
    #
    @7
    @5
    wss
    #
    wa
    #
    vw
    @3
    wrex
    #
    wi
    #
    vz
    cJ
    wral
    #
    wa
    #
    cn
    cJ
    vf
    cv
    #
    wf
    #
    cA
    vk
    cv
    #
    @15
    cfv
    #
    wcel
    #
    @17
    c1
    caddc
    co
    #
    @15
    cfv
    #
    @18
    wss
    #
    wa
    #
    vk
    cn
    wral
    #
    cA
    vy
    cv
    #
    wcel
    #
    @18
    @25
    wss
    #
    vk
    cn
    wrex
    #
    wi
    #
    vy
    cJ
    wral
    #
    w3a
    #
    vf
    wex
    #
    vx
    cJ
    cpw
    #
    vx
    vz
    vw
    cA
    cJ
    cX
    1stcclb.1
    1stcclb
    @2
    @3
    @33
    wcel
    #
    @14
    wa
    #
    wa
    #
    cn
    cA
    va
    cv
    #
    wcel
    #
    va
    @3
    crab
    #
    vg
    cv
    #
    wfo
    #
    vg
    wex
    #
    @32
    @36
    c0
    @39
    csdm
    wbr
    #
    @39
    cn
    cdom
    wbr
    #
    @42
    @36
    @39
    c0
    wne
    #
    @43
    @36
    @38
    va
    @3
    wrex
    #
    @45
    @36
    @8
    vw
    @3
    wrex
    #
    @46
    @36
    @8
    @7
    cX
    wss
    #
    wa
    #
    vw
    @3
    wrex
    #
    @47
    @36
    cX
    cJ
    wcel
    #
    @13
    @1
    @50
    @36
    cJ
    ctop
    wcel
    #
    @51
    @0
    @52
    @1
    @35
    cJ
    1stctop
    #
    ad2antrr
    cJ
    cX
    1stcclb.1
    topopn
    syl
    @2
    @34
    @4
    @13
    simprrr
    @0
    @1
    @35
    simplr
    @12
    @1
    @50
    wi
    vz
    cX
    cJ
    @5
    cX
    wceq
    #
    @6
    @1
    @11
    @50
    @5
    cX
    cA
    eleq2
    @54
    @10
    @49
    vw
    @3
    @54
    @9
    @48
    @8
    @5
    cX
    @7
    sseq2
    anbi2d
    rexbidv
    imbi12d
    rspcv
    syl3c
    @49
    @8
    vw
    @3
    @8
    @48
    simpl
    reximi
    syl
    @8
    @38
    vw
    va
    @3
    @7
    @37
    cA
    eleq2
    cbvrexv
    sylib
    @38
    va
    @3
    rabn0
    sylibr
    @39
    @38
    va
    @3
    vx
    vex
    #
    rabex
    0sdom
    sylibr
    @36
    @39
    @3
    cdom
    wbr
    #
    @3
    cn
    cdom
    wbr
    #
    @44
    @3
    cvv
    wcel
    @39
    @3
    wss
    @56
    @55
    @38
    va
    @3
    ssrab2
    #
    @39
    @3
    cvv
    ssdomg
    mp2
    @36
    @4
    com
    cn
    cen
    wbr
    @57
    @2
    @34
    @4
    @13
    simprrl
    cn
    com
    nnenom
    ensymi
    @3
    com
    cn
    domentr
    sylancl
    @39
    @3
    cn
    domtr
    sylancr
    cn
    @39
    vg
    fodomr
    syl2anc
    @36
    @41
    @32
    vg
    @2
    @34
    @13
    @41
    @32
    wi
    @4
    @2
    @34
    @13
    wa
    #
    @41
    @32
    @2
    @59
    @41
    wa
    #
    wa
    #
    cn
    cJ
    vn
    cn
    @40
    c1
    vn
    cv
    #
    cfz
    co
    #
    cima
    #
    cint
    #
    cmpt
    #
    wf
    #
    cA
    @17
    @66
    cfv
    #
    wcel
    #
    @20
    @66
    cfv
    #
    @68
    wss
    #
    wa
    #
    vk
    cn
    wral
    #
    @26
    @68
    @25
    wss
    #
    vk
    cn
    wrex
    #
    wi
    #
    vy
    cJ
    wral
    #
    @32
    @61
    vn
    cn
    @65
    cJ
    @66
    @61
    @62
    cn
    wcel
    #
    wa
    #
    @52
    @64
    cJ
    wss
    #
    @64
    c0
    wne
    #
    @64
    cfn
    wcel
    #
    @65
    cJ
    wcel
    #
    @0
    @52
    @1
    @60
    @78
    @53
    ad3antrrr
    @79
    @64
    @40
    crn
    #
    cJ
    @40
    @63
    imassrn
    @61
    @84
    cJ
    wss
    @78
    @61
    @84
    @39
    cJ
    @41
    @84
    @39
    wceq
    #
    @2
    @59
    cn
    @39
    @40
    forn
    ad2antll
    #
    @61
    @39
    @3
    cJ
    @58
    @61
    @3
    cJ
    @2
    @34
    @13
    @41
    simprll
    elpwid
    syl5ss
    eqsstrd
    adantr
    syl5ss
    @79
    @40
    cdm
    #
    @63
    cin
    #
    c0
    wne
    @81
    @79
    @88
    @63
    c0
    @79
    @63
    @87
    wss
    #
    @88
    @63
    wceq
    @61
    @89
    @78
    @61
    cn
    @63
    @87
    vk
    @63
    cn
    @17
    @62
    elfznn
    ssriv
    @61
    cn
    @39
    @40
    wf
    #
    @87
    cn
    wceq
    #
    @41
    @90
    @2
    @59
    cn
    @39
    @40
    fof
    ad2antll
    #
    cn
    @39
    @40
    fdm
    syl
    #
    syl5sseqr
    adantr
    #
    @63
    @87
    sseqin2
    sylib
    @78
    @61
    @62
    @63
    wcel
    #
    @63
    c0
    wne
    #
    @62
    elfz1end
    @95
    @96
    @61
    @63
    @62
    ne0i
    adantl
    sylan2b
    eqnetrd
    @64
    c0
    @88
    c0
    @40
    @63
    imadisj
    necon3bii
    sylibr
    @79
    @63
    cfn
    wcel
    @63
    @64
    @40
    @63
    cres
    #
    wfo
    #
    @82
    @79
    c1
    @62
    fzfid
    @79
    @40
    wfun
    #
    @89
    @98
    @61
    @99
    @78
    @61
    @90
    @99
    @92
    cn
    @39
    @40
    ffun
    syl
    #
    adantr
    @94
    @63
    @40
    fores
    syl2anc
    @63
    @64
    @97
    fofi
    syl2anc
    @52
    @80
    @81
    @82
    w3a
    @83
    @64
    cJ
    fiinopn
    imp
    syl13anc
    #
    @66
    eqid
    #
    fmptd
    @61
    @72
    vk
    cn
    @61
    @17
    cn
    wcel
    #
    wa
    #
    @69
    @71
    @104
    cA
    @40
    c1
    @17
    cfz
    co
    #
    cima
    #
    cint
    #
    @68
    @104
    cA
    @107
    wcel
    #
    cA
    @62
    wcel
    #
    vn
    @106
    wral
    #
    @104
    @106
    @39
    wss
    @109
    vn
    @39
    wral
    #
    @110
    @104
    @84
    @106
    @39
    @40
    @105
    imassrn
    @61
    @85
    @103
    @86
    adantr
    syl5sseq
    @111
    @109
    @109
    wi
    #
    vn
    @3
    wral
    @112
    vn
    @3
    @109
    id
    rgenw
    @38
    @109
    @109
    vn
    va
    @3
    @37
    @62
    cA
    eleq2
    ralrab
    mpbir
    @109
    vn
    @106
    @39
    ssralv
    mpisyl
    @1
    @108
    @110
    wb
    @0
    @60
    @103
    vn
    cA
    @106
    cX
    elintg
    ad3antlr
    mpbird
    @104
    @103
    @107
    cJ
    wcel
    #
    @68
    @107
    wceq
    @61
    @103
    simpr
    @61
    @83
    vn
    cn
    wral
    #
    @103
    @113
    @61
    @83
    vn
    cn
    @101
    ralrimiva
    #
    @83
    @113
    vn
    @17
    cn
    vn
    vk
    weq
    #
    @65
    @107
    cJ
    @116
    @64
    @106
    @116
    @63
    @105
    @40
    @62
    @17
    c1
    cfz
    oveq2
    imaeq2d
    inteqd
    #
    eleq1d
    rspccva
    sylan
    vn
    @17
    @65
    @107
    cn
    cJ
    @66
    @117
    @102
    fvmptg
    syl2anc
    #
    eleqtrrd
    @104
    @40
    c1
    @20
    cfz
    co
    #
    cima
    #
    cint
    #
    @107
    @70
    @68
    @104
    @106
    @120
    wss
    #
    @121
    @107
    wss
    @105
    @119
    wss
    @122
    @104
    c1
    @17
    fzssp1
    @105
    @119
    @40
    imass2
    mp1i
    @106
    @120
    intss
    syl
    @104
    @20
    cn
    wcel
    #
    @121
    cJ
    wcel
    #
    @70
    @121
    wceq
    @103
    @123
    @61
    @17
    peano2nn
    #
    adantl
    @61
    @114
    @123
    @124
    @103
    @115
    @125
    @83
    @124
    vn
    @20
    cn
    @62
    @20
    wceq
    #
    @65
    @121
    cJ
    @126
    @64
    @120
    @126
    @63
    @119
    @40
    @62
    @20
    c1
    cfz
    oveq2
    imaeq2d
    inteqd
    #
    eleq1d
    rspccva
    syl2an
    vn
    @20
    @65
    @121
    cn
    cJ
    @66
    @127
    @102
    fvmptg
    syl2anc
    @118
    3sstr4d
    jca
    ralrimiva
    @61
    @76
    vy
    cJ
    @61
    @25
    cJ
    wcel
    #
    wa
    #
    @26
    @107
    @25
    wss
    #
    vk
    cn
    wrex
    #
    @75
    @129
    @26
    @8
    @7
    @25
    wss
    #
    wa
    #
    vw
    @3
    wrex
    #
    @131
    @61
    @13
    @128
    @26
    @134
    wi
    #
    @2
    @34
    @13
    @41
    simprlr
    @12
    @135
    vz
    @25
    cJ
    vz
    vy
    weq
    #
    @6
    @26
    @11
    @134
    @5
    @25
    cA
    eleq2
    @136
    @10
    @133
    vw
    @3
    @136
    @9
    @132
    @8
    @5
    @25
    @7
    sseq2
    anbi2d
    rexbidv
    imbi12d
    rspccva
    sylan
    @134
    @132
    vw
    @39
    wrex
    #
    @129
    @131
    @38
    @8
    @132
    vw
    va
    @3
    @37
    @7
    cA
    eleq2
    rexrab
    @129
    @137
    @17
    @40
    cfv
    #
    @25
    wss
    #
    vk
    cn
    wrex
    #
    @131
    @61
    @137
    @140
    wb
    @128
    @61
    @132
    vw
    @84
    wrex
    #
    @137
    @140
    @61
    @132
    vw
    @84
    @39
    @86
    rexeqdv
    @61
    @40
    cn
    wfn
    #
    @141
    @140
    wb
    @41
    @142
    @2
    @59
    cn
    @39
    @40
    fofn
    ad2antll
    @132
    @139
    vw
    vk
    cn
    @40
    @7
    @138
    @25
    sseq1
    rexrn
    syl
    bitr3d
    adantr
    @129
    @139
    @130
    vk
    cn
    @129
    @103
    wa
    @138
    @106
    wcel
    #
    @107
    @138
    wss
    @139
    @130
    wi
    @103
    @129
    @17
    @105
    wcel
    #
    @143
    @17
    elfz1end
    @129
    @144
    @143
    @129
    @99
    @105
    @87
    wss
    @144
    @143
    wi
    @61
    @99
    @128
    @100
    adantr
    @129
    cn
    @105
    @87
    vn
    @105
    cn
    @62
    @17
    elfznn
    ssriv
    @61
    @91
    @128
    @93
    adantr
    syl5sseqr
    @105
    @17
    @40
    funfvima2
    syl2anc
    imp
    sylan2b
    @138
    @106
    intss1
    @107
    @138
    @25
    sstr2
    3syl
    reximdva
    sylbid
    syl5bir
    syld
    @61
    @75
    @131
    wb
    @128
    @61
    @74
    @130
    vk
    cn
    @104
    @68
    @107
    @25
    @118
    sseq1d
    rexbidva
    adantr
    sylibrd
    ralrimiva
    @31
    @67
    @73
    @77
    w3a
    vf
    @66
    vn
    cn
    @65
    nnex
    mptex
    @15
    @66
    wceq
    #
    @16
    @67
    @24
    @73
    @30
    @77
    cn
    cJ
    @15
    @66
    feq1
    @145
    @23
    @72
    vk
    cn
    @145
    @19
    @69
    @22
    @71
    @145
    @18
    @68
    cA
    @17
    @15
    @66
    fveq1
    #
    eleq2d
    @145
    @21
    @70
    @18
    @68
    @20
    @15
    @66
    fveq1
    @146
    sseq12d
    anbi12d
    ralbidv
    @145
    @29
    @76
    vy
    cJ
    @145
    @28
    @75
    @26
    @145
    @27
    @74
    vk
    cn
    @145
    @18
    @68
    @25
    @146
    sseq1d
    rexbidv
    imbi2d
    ralbidv
    3anbi123d
    spcev
    syl3anc
    expr
    adantrrl
    exlimdv
    mpd
    rexlimddv
end
