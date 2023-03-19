include "cv.mm"
include "wf.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "wfun.mm"
include "cdm.mm"
include "crn.mm"
include "w3a.mm"
include "cref.mm"
include "wbr.mm"
include "clocfin.mm"
include "wcel.mm"
include "cuni.mm"
include "wb.mm"
include "reff.mm"
include "syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cmpt.mm"
include "funmpt.mm"
include "a1i.mm"
include "eqid.mm"
include "dmmptss.mm"
include "frn.mm"
include "ad2antlr.mm"
include "syl5ss.mm"
include "ctop.mm"
include "locfintop.mm"
include "ad3antrrr.mm"
include "cnvimass.mm"
include "wceq.mm"
include "fdm.mm"
include "ad3antlr.mm"
include "syl5sseq.mm"
include "sstrd.mm"
include "uniopn.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "rnmptss.mm"
include "wrex.mm"
include "ciun.mm"
include "refbas.mm"
include "ad2antrr.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfre1.mm"
include "wfn.mm"
include "ffn.mm"
include "ad4antlr.mm"
include "simplr.mm"
include "fnfvelrn.mm"
include "ssid.mm"
include "fniniseg.mm"
include "biimpar.mm"
include "mpanr2.mm"
include "sylancom.mm"
include "ssuni.mm"
include "sylancr.mm"
include "sselda.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "unieqd.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "adantllr.mm"
include "simpr.mm"
include "r19.29af.mm"
include "sseldd.mm"
include "eluni2.mm"
include "sylib.mm"
include "reximd2a.mm"
include "r19.29an.mm"
include "impbida.mm"
include "eliun.mm"
include "3bitr4g.mm"
include "eqrdv.mm"
include "dfiun3g.mm"
include "3eqtrd.mm"
include "cvv.mm"
include "vex.mm"
include "elrnmpt.mm"
include "mp1i.mm"
include "biimpa.mm"
include "ssrexv.mm"
include "sylc.mm"
include "nfmpt1.mm"
include "nfrn.mm"
include "nfcri.mm"
include "simp-5r.mm"
include "ad5antlr.mm"
include "simpld.mm"
include "rspa.mm"
include "sseqtrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "unissb.mm"
include "sylibr.mm"
include "eqsstrd.mm"
include "exp31.mm"
include "reximdai.mm"
include "mpd.mm"
include "rnex.mm"
include "mptex.mm"
include "rnexg.mm"
include "isref.mm"
include "mpbir2and.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "crab.mm"
include "cfn.mm"
include "eqtrd.mm"
include "cdom.mm"
include "ffun.mm"
include "ad6antlr.mm"
include "imafi.mm"
include "simp3.mm"
include "cnvex.mm"
include "imaexg.mm"
include "ax-mp.mm"
include "uniex.mm"
include "fvmpt.mm"
include "3ad2ant2.mm"
include "ineq1d.mm"
include "neeq1d.mm"
include "wfo.mm"
include "fnmpti.mm"
include "dffn4.mm"
include "mpbi.mm"
include "rabfodom.mm"
include "cbvrabv.mm"
include "syl6breq.mm"
include "rabex.mm"
include "nfrab1.mm"
include "nfel1.mm"
include "nfrex.mm"
include "ad5antr.mm"
include "rabid.mm"
include "sylanbrc.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "uniinn0.mm"
include "biimpi.mm"
include "adantl.mm"
include "r19.29af2.mm"
include "ss2rabdv.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "domtr.mm"
include "adantr.mm"
include "dffn3.mm"
include "ssrab2.mm"
include "fimarab.mm"
include "mpan2.mm"
include "3syl.mm"
include "breqtrrd.mm"
include "domfi.mm"
include "imdistanda.mm"
include "imp.mm"
include "simplll.mm"
include "islocfin.mm"
include "simp3d.mm"
include "r19.21bi.mm"
include "syl3anbrc.mm"
include "funeq.mm"
include "dmeq.mm"
include "sseq1d.mm"
include "rneq.mm"
include "3anbi123d.mm"
include "breq1d.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl32anc.mm"
include "expl.mm"
include "exlimdv.mm"

theorem locfinreflem
  let wph: wff ph
  let cU: class U
  let vf: setvar f
  let cJ: class J
  let cV: class V
  let cX: class X
  let vg: setvar g
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  assume locfinref.x: |- X = U. J
  assume locfinref.1: |- ( ph -> U C_ J )
  assume locfinref.2: |- ( ph -> X = U. U )
  assume locfinref.3: |- ( ph -> V C_ J )
  assume locfinref.4: |- ( ph -> V Ref U )
  assume locfinref.5: |- ( ph -> V e. ( LocFin ` J ) )

  disjoint J f
  disjoint U f
  disjoint V f
  disjoint f ph
  disjoint J g
  disjoint J j
  disjoint J k
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint f g
  disjoint f j
  disjoint f k
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint g j
  disjoint g k
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint j k
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint v w
  disjoint v x
  disjoint w x
  disjoint U g
  disjoint U j
  disjoint U k
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U x
  disjoint V g
  disjoint V j
  disjoint V k
  disjoint V u
  disjoint V v
  disjoint V w
  disjoint V x
  disjoint X j
  disjoint X k
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint g ph
  disjoint j ph
  disjoint k ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  assert |- ( ph -> E. f ( ( Fun f /\ dom f C_ U /\ ran f C_ J ) /\ ( ran f Ref U /\ ran f e. ( LocFin ` J ) ) ) )

  proof
    wph
    cV
    cU
    vg
    cv
    #
    wf
    #
    vv
    cv
    #
    @2
    @0
    cfv
    #
    wss
    #
    vv
    cV
    wral
    #
    wa
    #
    vg
    wex
    #
    vf
    cv
    #
    wfun
    #
    @8
    cdm
    #
    cU
    wss
    #
    @8
    crn
    #
    cJ
    wss
    #
    w3a
    #
    @12
    cU
    cref
    wbr
    #
    @12
    cJ
    clocfin
    cfv
    #
    wcel
    #
    wa
    #
    wa
    #
    vf
    wex
    #
    wph
    cU
    cuni
    #
    cV
    cuni
    #
    wss
    #
    @7
    wph
    cV
    cU
    cref
    wbr
    #
    @23
    @7
    wa
    #
    locfinref.4
    wph
    cV
    @16
    wcel
    #
    @24
    @25
    wb
    locfinref.5
    vv
    cV
    cU
    vg
    @16
    reff
    syl
    mpbid
    simprd
    wph
    @6
    @20
    vg
    wph
    @1
    @5
    @20
    wph
    @1
    wa
    #
    @5
    wa
    #
    vu
    @0
    crn
    #
    @0
    ccnv
    #
    vu
    cv
    #
    csn
    #
    cima
    #
    cuni
    #
    cmpt
    #
    wfun
    #
    @35
    cdm
    #
    cU
    wss
    #
    @35
    crn
    #
    cJ
    wss
    #
    @39
    cU
    cref
    wbr
    #
    @39
    @16
    wcel
    #
    @20
    @36
    @28
    vu
    @29
    @34
    funmpt
    a1i
    @28
    @37
    @29
    cU
    vu
    @29
    @34
    @35
    @35
    eqid
    #
    dmmptss
    @1
    @29
    cU
    wss
    #
    wph
    @5
    cV
    cU
    @0
    frn
    #
    ad2antlr
    syl5ss
    @28
    @34
    cJ
    wcel
    #
    vu
    @29
    wral
    #
    @40
    @28
    @46
    vu
    @29
    @28
    @31
    @29
    wcel
    #
    wa
    #
    cJ
    ctop
    wcel
    #
    @33
    cJ
    wss
    @46
    wph
    @50
    @1
    @5
    @48
    wph
    @26
    @50
    locfinref.5
    cV
    cJ
    locfintop
    syl
    #
    ad3antrrr
    @49
    @33
    cV
    cJ
    @49
    @0
    cdm
    #
    @33
    cV
    @0
    @32
    cnvimass
    @1
    @52
    cV
    wceq
    wph
    @5
    @48
    cV
    cU
    @0
    fdm
    ad3antlr
    syl5sseq
    #
    wph
    cV
    cJ
    wss
    @1
    @5
    @48
    locfinref.3
    ad3antrrr
    sstrd
    @33
    cJ
    uniopn
    syl2anc
    ralrimiva
    #
    vu
    @29
    @34
    cJ
    @35
    @43
    rnmptss
    syl
    @28
    @41
    @21
    @39
    cuni
    #
    wceq
    #
    vw
    cv
    #
    @31
    wss
    #
    vu
    cU
    wrex
    #
    vw
    @39
    wral
    #
    @28
    @21
    @22
    vu
    @29
    @34
    ciun
    #
    @55
    wph
    @21
    @22
    wceq
    #
    @1
    @5
    wph
    @24
    @62
    locfinref.4
    cV
    cU
    @22
    @21
    @22
    eqid
    #
    @21
    eqid
    #
    refbas
    syl
    ad2antrr
    @28
    vx
    @22
    @61
    @28
    vx
    cv
    #
    @2
    wcel
    #
    vv
    cV
    wrex
    #
    @65
    @34
    wcel
    #
    vu
    @29
    wrex
    #
    @65
    @22
    wcel
    @65
    @61
    wcel
    @28
    @67
    @69
    @28
    @67
    wa
    @66
    @69
    vv
    cV
    @28
    @67
    vv
    @27
    @5
    vv
    @27
    vv
    nfv
    @4
    vv
    cV
    nfra1
    nfan
    #
    @66
    vv
    cV
    nfre1
    nfan
    @28
    @2
    cV
    wcel
    #
    @66
    @69
    @67
    @28
    @71
    wa
    #
    @66
    wa
    #
    @3
    @29
    wcel
    #
    @65
    @30
    @3
    csn
    #
    cima
    #
    cuni
    #
    wcel
    #
    @69
    @73
    @0
    cV
    wfn
    #
    @71
    @74
    @1
    @79
    wph
    @5
    @71
    @66
    cV
    cU
    @0
    ffn
    #
    ad4antlr
    @28
    @71
    @66
    simplr
    cV
    @2
    @0
    fnfvelrn
    syl2anc
    @72
    @2
    @77
    @65
    @72
    @2
    @2
    wss
    @2
    @76
    wcel
    #
    @2
    @77
    wss
    @2
    ssid
    @28
    @71
    @79
    @81
    @1
    @79
    wph
    @5
    @71
    @80
    ad3antlr
    @79
    @71
    @3
    @3
    wceq
    #
    @81
    @3
    eqid
    @79
    @81
    @71
    @82
    wa
    cV
    @3
    @2
    @0
    fniniseg
    biimpar
    mpanr2
    sylancom
    @2
    @2
    @76
    ssuni
    sylancr
    sselda
    @68
    @78
    vu
    @3
    @29
    @31
    @3
    wceq
    #
    @34
    @77
    @65
    @83
    @33
    @76
    @83
    @32
    @75
    @30
    @31
    @3
    sneq
    imaeq2d
    unieqd
    eleq2d
    rspcev
    syl2anc
    adantllr
    @28
    @67
    simpr
    r19.29af
    @28
    @68
    @67
    vu
    @29
    @49
    @68
    wa
    #
    @66
    @66
    vv
    @33
    cV
    @49
    @68
    vv
    @28
    @48
    vv
    @70
    @48
    vv
    nfv
    nfan
    @68
    vv
    nfv
    nfan
    @84
    @2
    @33
    wcel
    #
    wa
    #
    @66
    wa
    @33
    cV
    @2
    @49
    @33
    cV
    wss
    @68
    @85
    @66
    @53
    ad3antrrr
    @84
    @85
    @66
    simplr
    sseldd
    @86
    @66
    simpr
    @84
    @68
    @66
    vv
    @33
    wrex
    @49
    @68
    simpr
    vv
    @65
    @33
    eluni2
    sylib
    reximd2a
    r19.29an
    impbida
    vv
    @65
    cV
    eluni2
    vu
    @65
    @29
    @34
    eliun
    3bitr4g
    eqrdv
    @28
    @47
    @61
    @55
    wceq
    @54
    vu
    @29
    @34
    cJ
    dfiun3g
    syl
    3eqtrd
    #
    @28
    @59
    vw
    @39
    @28
    @57
    @39
    wcel
    #
    wa
    #
    @57
    @34
    wceq
    #
    vu
    cU
    wrex
    #
    @59
    @89
    @44
    @90
    vu
    @29
    wrex
    #
    @91
    @1
    @44
    wph
    @5
    @88
    @45
    ad3antlr
    @28
    @88
    @92
    @57
    cvv
    wcel
    @88
    @92
    wb
    @28
    vw
    vex
    vu
    @29
    @34
    @57
    @35
    cvv
    @43
    elrnmpt
    mp1i
    biimpa
    @90
    vu
    @29
    cU
    ssrexv
    sylc
    @89
    @90
    @58
    vu
    cU
    @28
    @88
    vu
    @28
    vu
    nfv
    vu
    vw
    @39
    vu
    @35
    vu
    @29
    @34
    nfmpt1
    nfrn
    nfcri
    nfan
    @89
    @31
    cU
    wcel
    #
    @90
    @58
    @89
    @93
    wa
    #
    @90
    wa
    #
    @57
    @34
    @31
    @94
    @90
    simpr
    @95
    @2
    @31
    wss
    #
    vv
    @33
    wral
    @34
    @31
    wss
    @95
    @96
    vv
    @33
    @94
    @90
    vv
    @89
    @93
    vv
    @28
    @88
    vv
    @70
    @88
    vv
    nfv
    nfan
    @93
    vv
    nfv
    nfan
    @90
    vv
    nfv
    nfan
    @95
    @85
    @96
    @95
    @85
    wa
    #
    @2
    @3
    @31
    @97
    @5
    @71
    @4
    @27
    @5
    @88
    @93
    @90
    @85
    simp-5r
    @97
    @71
    @3
    @31
    wceq
    #
    @95
    @85
    @71
    @98
    wa
    #
    @95
    @79
    @85
    @99
    wb
    @1
    @79
    wph
    @5
    @88
    @93
    @90
    @80
    ad5antlr
    cV
    @31
    @2
    @0
    fniniseg
    syl
    biimpa
    #
    simpld
    @4
    vv
    cV
    rspa
    syl2anc
    @97
    @71
    @98
    @100
    simprd
    sseqtrd
    ex
    ralrimi
    vv
    @33
    @31
    unissb
    sylibr
    eqsstrd
    exp31
    reximdai
    mpd
    ralrimiva
    @28
    @39
    cvv
    wcel
    #
    @41
    @56
    @60
    wa
    wb
    @35
    cvv
    wcel
    @101
    @28
    vu
    @29
    @34
    @0
    vg
    vex
    #
    rnex
    #
    mptex
    #
    @35
    cvv
    rnexg
    mp1i
    vw
    vu
    @39
    cU
    cvv
    @55
    @21
    @55
    eqid
    #
    @64
    isref
    syl
    mpbir2and
    @28
    @50
    cX
    @55
    wceq
    @66
    @57
    @2
    cin
    #
    c0
    wne
    #
    vw
    @39
    crab
    #
    cfn
    wcel
    #
    wa
    #
    vv
    cJ
    wrex
    #
    vx
    cX
    wral
    @42
    wph
    @50
    @1
    @5
    @51
    ad2antrr
    @28
    cX
    @21
    @55
    wph
    cX
    @21
    wceq
    @1
    @5
    locfinref.2
    ad2antrr
    @87
    eqtrd
    @28
    @111
    vx
    cX
    @28
    @65
    cX
    wcel
    #
    wa
    #
    @66
    vj
    cv
    #
    @2
    cin
    c0
    wne
    #
    vj
    cV
    crab
    #
    cfn
    wcel
    #
    wa
    #
    @110
    vv
    cJ
    cJ
    @28
    @112
    vv
    @70
    @112
    vv
    nfv
    nfan
    @113
    @2
    cJ
    wcel
    #
    @118
    simplr
    @113
    @119
    wa
    #
    @118
    @110
    @120
    @66
    @117
    @109
    @120
    @66
    wa
    #
    @117
    @109
    @121
    @117
    wa
    #
    @0
    @116
    cima
    #
    cfn
    wcel
    #
    @108
    @123
    cdom
    wbr
    @109
    @121
    @117
    @0
    wfun
    #
    @124
    @1
    @125
    wph
    @5
    @112
    @119
    @66
    @117
    cV
    cU
    @0
    ffun
    ad6antlr
    @0
    @116
    imafi
    sylancom
    @122
    @108
    vk
    cv
    #
    @0
    cfv
    #
    @31
    wceq
    #
    vk
    @116
    wrex
    #
    vu
    @29
    crab
    #
    @123
    cdom
    @122
    @108
    @34
    @2
    cin
    #
    c0
    wne
    #
    vu
    @29
    crab
    #
    cdom
    wbr
    @133
    @130
    cdom
    wbr
    #
    @108
    @130
    cdom
    wbr
    @122
    @108
    @30
    @126
    csn
    #
    cima
    #
    cuni
    #
    @2
    cin
    #
    c0
    wne
    #
    vk
    @29
    crab
    @133
    cdom
    @122
    @139
    @107
    vk
    vw
    @29
    @39
    @35
    cvv
    @122
    @126
    @29
    wcel
    #
    @57
    @126
    @35
    cfv
    #
    wceq
    #
    w3a
    #
    @106
    @138
    c0
    @143
    @57
    @137
    @2
    @143
    @57
    @141
    @137
    @122
    @140
    @142
    simp3
    @140
    @122
    @141
    @137
    wceq
    @142
    vu
    @126
    @34
    @137
    @29
    @35
    @31
    @126
    wceq
    #
    @33
    @136
    @144
    @32
    @135
    @30
    @31
    @126
    sneq
    imaeq2d
    unieqd
    @43
    @136
    @30
    cvv
    wcel
    #
    @136
    cvv
    wcel
    @0
    @102
    cnvex
    #
    @30
    @135
    cvv
    imaexg
    ax-mp
    uniex
    fvmpt
    3ad2ant2
    eqtrd
    ineq1d
    neeq1d
    @29
    cvv
    wcel
    @122
    @103
    a1i
    @29
    @39
    @35
    wfo
    #
    @122
    @35
    @29
    wfn
    @147
    vu
    @29
    @34
    @35
    @33
    @145
    @33
    cvv
    wcel
    @146
    @30
    @32
    cvv
    imaexg
    ax-mp
    uniex
    @43
    fnmpti
    @29
    @35
    dffn4
    mpbi
    a1i
    rabfodom
    @139
    @132
    vk
    vu
    @29
    @126
    @31
    wceq
    #
    @138
    @131
    c0
    @148
    @137
    @34
    @2
    @148
    @136
    @33
    @148
    @135
    @32
    @30
    @126
    @31
    sneq
    imaeq2d
    unieqd
    ineq1d
    neeq1d
    cbvrabv
    syl6breq
    @130
    cvv
    wcel
    @122
    @133
    @130
    wss
    @134
    @129
    vu
    @29
    @103
    rabex
    @122
    @132
    @129
    vu
    @29
    @122
    @48
    wa
    #
    @132
    @129
    @149
    @132
    wa
    #
    @115
    @129
    vj
    @33
    @149
    @132
    vj
    @122
    @48
    vj
    @121
    @117
    vj
    @121
    vj
    nfv
    vj
    @116
    cfn
    @115
    vj
    cV
    nfrab1
    #
    nfel1
    nfan
    @48
    vj
    nfv
    nfan
    @132
    vj
    nfv
    nfan
    @128
    vj
    vk
    @116
    @151
    @128
    vj
    nfv
    nfrex
    @150
    @114
    @33
    wcel
    #
    wa
    #
    @115
    wa
    #
    @114
    @116
    wcel
    #
    @114
    @0
    cfv
    #
    @31
    wceq
    #
    @129
    @154
    @114
    cV
    wcel
    #
    @115
    @155
    @154
    @158
    @157
    @154
    @79
    @152
    @158
    @157
    wa
    #
    @121
    @79
    @117
    @48
    @132
    @152
    @115
    @1
    @79
    wph
    @5
    @112
    @119
    @66
    @80
    ad5antlr
    #
    ad5antr
    @150
    @152
    @115
    simplr
    @79
    @152
    @159
    cV
    @31
    @114
    @0
    fniniseg
    biimpa
    syl2anc
    #
    simpld
    @153
    @115
    simpr
    @115
    vj
    cV
    rabid
    sylanbrc
    @154
    @158
    @157
    @161
    simprd
    @128
    @157
    vk
    @114
    @116
    @126
    @114
    wceq
    @127
    @156
    @31
    @126
    @114
    @0
    fveq2
    eqeq1d
    rspcev
    syl2anc
    @132
    @115
    vj
    @33
    wrex
    #
    @149
    @132
    @162
    vj
    @33
    @2
    uniinn0
    biimpi
    adantl
    r19.29af2
    ex
    ss2rabdv
    @133
    @130
    cvv
    ssdomg
    mpsyl
    @108
    @133
    @130
    domtr
    syl2anc
    @122
    @79
    cV
    @29
    @0
    wf
    #
    @123
    @130
    wceq
    #
    @121
    @79
    @117
    @160
    adantr
    @79
    @163
    cV
    @0
    dffn3
    biimpi
    @163
    @116
    cV
    wss
    @164
    @115
    vj
    cV
    ssrab2
    vk
    vu
    cV
    @29
    @0
    @116
    fimarab
    mpan2
    3syl
    breqtrrd
    @123
    @108
    domfi
    syl2anc
    ex
    imdistanda
    imp
    @28
    @112
    wph
    @118
    vv
    cJ
    wrex
    #
    wph
    @1
    @5
    @112
    simplll
    wph
    @165
    vx
    cX
    wph
    @50
    cX
    @22
    wceq
    #
    @165
    vx
    cX
    wral
    #
    wph
    @26
    @50
    @166
    @167
    w3a
    locfinref.5
    vx
    cV
    vv
    cJ
    cX
    @22
    vj
    locfinref.x
    @63
    islocfin
    sylib
    simp3d
    r19.21bi
    sylancom
    reximd2a
    ralrimiva
    vx
    @39
    vv
    cJ
    cX
    @55
    vw
    locfinref.x
    @105
    islocfin
    syl3anbrc
    @19
    @36
    @38
    @40
    w3a
    #
    @41
    @42
    wa
    #
    wa
    vf
    @35
    @104
    @8
    @35
    wceq
    #
    @14
    @168
    @18
    @169
    @170
    @9
    @36
    @11
    @38
    @13
    @40
    @8
    @35
    funeq
    @170
    @10
    @37
    cU
    @8
    @35
    dmeq
    sseq1d
    @170
    @12
    @39
    cJ
    @8
    @35
    rneq
    #
    sseq1d
    3anbi123d
    @170
    @15
    @41
    @17
    @42
    @170
    @12
    @39
    cU
    cref
    @171
    breq1d
    @170
    @12
    @39
    @16
    @171
    eleq1d
    anbi12d
    anbi12d
    spcev
    syl32anc
    expl
    exlimdv
    mpd
end
