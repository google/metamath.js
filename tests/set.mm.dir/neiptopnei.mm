include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "csn.mm"
include "cnei.mm"
include "cpw.mm"
include "feqmptd.mm"
include "wcel.mm"
include "wa.mm"
include "cuni.mm"
include "wss.mm"
include "wel.mm"
include "wrex.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "elpwid.mm"
include "simpr.mm"
include "sseldd.mm"
include "wceq.mm"
include "neiptopuni.mm"
include "sseqtrd.mm"
include "crab.mm"
include "wral.mm"
include "ssrab2.mm"
include "a1i.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "elrab.mm"
include "simp-5l.mm"
include "simpr1l.mm"
include "3anassrs.mm"
include "simplr.mm"
include "w3a.mm"
include "wi.mm"
include "sseq1.mm"
include "3anbi2d.mm"
include "eleq1.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "simpl1l.mm"
include "cvv.mm"
include "ctop.mm"
include "neiptoptop.mm"
include "uniexg.mm"
include "syl.mm"
include "eqeltrd.mm"
include "rabexg.mm"
include "sseq2.mm"
include "3anbi23d.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "anbi2d.mm"
include "3anbi1d.mm"
include "chvarv.mm"
include "vtoclg.mm"
include "3syl.mm"
include "mpcom.mm"
include "3an1rs.mm"
include "mpan2.mm"
include "syl211anc.mm"
include "simplll.mm"
include "simprl.mm"
include "simprr.mm"
include "wb.mm"
include "cbvralv.mm"
include "rexeqbidv.mm"
include "rexralbidv.mm"
include "sselda.mm"
include "a1d.mm"
include "ancrd.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "mpd.mm"
include "ralbii.mm"
include "rexbii.mm"
include "sylibr.mm"
include "dfss3.mm"
include "biimpri.mm"
include "reximi.mm"
include "syl21anc.mm"
include "r19.29a.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "neipeltop.mm"
include "sylanbrc.mm"
include "anim1i.mm"
include "nfv.mm"
include "nfrab1.mm"
include "nfcv.mm"
include "rabid.mm"
include "elequ1.mm"
include "elequ2.mm"
include "ex.mm"
include "syl5bi.mm"
include "ssrd.mm"
include "eleq2.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "jca.mm"
include "nfre1.mm"
include "nfan.mm"
include "sseqtr4d.mm"
include "syl31anc.mm"
include "simprbi.mm"
include "r19.21bi.mm"
include "anasss.mm"
include "reximi2.mm"
include "ad2antll.mm"
include "r19.29af.mm"
include "impbida.mm"
include "eleqtrd.mm"
include "eqid.mm"
include "isneip.mm"
include "syl2anc.mm"
include "bitr4d.mm"
include "eqrdv.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"

theorem neiptopnei
  let wph: wff ph
  let cJ: class J
  let cN: class N
  let cX: class X
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let cC: class C
  let vc: setvar c
  let ve: setvar e
  let vf: setvar f
  let vd: setvar d
  let vr: setvar r
  let vs: setvar s
  assume neiptop.o: |- J = { a e. ~P X | A. p e. a a e. ( N ` p ) }
  assume neiptop.0: |- ( ph -> N : X --> ~P ~P X )
  assume neiptop.1: |- ( ( ( ( ph /\ p e. X ) /\ a C_ b /\ b C_ X ) /\ a e. ( N ` p ) ) -> b e. ( N ` p ) )
  assume neiptop.2: |- ( ( ph /\ p e. X ) -> ( fi ` ( N ` p ) ) C_ ( N ` p ) )
  assume neiptop.3: |- ( ( ( ph /\ p e. X ) /\ a e. ( N ` p ) ) -> p e. a )
  assume neiptop.4: |- ( ( ( ph /\ p e. X ) /\ a e. ( N ` p ) ) -> E. b e. ( N ` p ) A. q e. b a e. ( N ` q ) )
  assume neiptop.5: |- ( ( ph /\ p e. X ) -> X e. ( N ` p ) )

  disjoint a p
  disjoint N a
  disjoint X a
  disjoint a b
  disjoint b p
  disjoint J a
  disjoint J p
  disjoint X p
  disjoint p ph
  disjoint N b
  disjoint X b
  disjoint a ph
  disjoint b ph
  disjoint a q
  disjoint b q
  disjoint p q
  disjoint N p
  disjoint N q
  disjoint X q
  disjoint ph q
  disjoint C a
  disjoint C p
  disjoint a c
  disjoint a e
  disjoint a f
  disjoint c e
  disjoint c f
  disjoint c p
  disjoint J c
  disjoint e f
  disjoint e p
  disjoint J e
  disjoint f p
  disjoint J f
  disjoint b c
  disjoint N c
  disjoint b e
  disjoint b f
  disjoint c ph
  disjoint e ph
  disjoint f ph
  disjoint a d
  disjoint c d
  disjoint d p
  disjoint J d
  disjoint a r
  disjoint a s
  disjoint b d
  disjoint b r
  disjoint b s
  disjoint c q
  disjoint c r
  disjoint c s
  disjoint d q
  disjoint d r
  disjoint d s
  disjoint N d
  disjoint p r
  disjoint p s
  disjoint q r
  disjoint q s
  disjoint r s
  disjoint N r
  disjoint N s
  disjoint X c
  disjoint X d
  disjoint X r
  disjoint X s
  disjoint d ph
  disjoint ph r
  disjoint ph s
  assert |- ( ph -> N = ( p e. X |-> ( ( nei ` J ) ` { p } ) ) )

  proof
    wph
    cN
    vp
    cX
    vp
    cv
    #
    cN
    cfv
    #
    cmpt
    vp
    cX
    @0
    csn
    cJ
    cnei
    cfv
    cfv
    #
    cmpt
    wph
    vp
    cX
    cX
    cpw
    #
    cpw
    #
    cN
    neiptop.0
    feqmptd
    wph
    vp
    cX
    @1
    @2
    wph
    @0
    cX
    wcel
    #
    wa
    #
    vc
    @1
    @2
    @6
    vc
    cv
    #
    @1
    wcel
    #
    @7
    cJ
    cuni
    #
    wss
    #
    vp
    vd
    wel
    #
    vd
    cv
    #
    @7
    wss
    #
    wa
    #
    vd
    cJ
    wrex
    #
    wa
    #
    @7
    @2
    wcel
    #
    @6
    @8
    @16
    @6
    @8
    wa
    #
    @10
    @15
    @18
    @7
    cX
    @9
    @18
    @7
    cX
    @18
    @1
    @3
    @7
    @18
    @1
    @3
    @6
    @1
    @4
    wcel
    @8
    wph
    cX
    @4
    @0
    cN
    neiptop.0
    ffvelrnda
    adantr
    elpwid
    @6
    @8
    simpr
    sseldd
    elpwid
    @6
    cX
    @9
    wceq
    #
    @8
    wph
    @19
    @5
    wph
    cJ
    cN
    cX
    vq
    vp
    va
    vb
    neiptop.o
    neiptop.0
    neiptop.1
    neiptop.2
    neiptop.3
    neiptop.4
    neiptop.5
    neiptopuni
    #
    adantr
    #
    adantr
    sseqtrd
    @18
    @7
    vq
    cv
    #
    cN
    cfv
    #
    wcel
    #
    vq
    cX
    crab
    #
    cJ
    wcel
    #
    @0
    @25
    wcel
    #
    @25
    @7
    wss
    #
    @15
    @18
    @25
    cX
    wss
    #
    @25
    @1
    wcel
    #
    vp
    @25
    wral
    #
    @26
    @29
    @18
    @24
    vq
    cX
    ssrab2
    #
    a1i
    @18
    @25
    vr
    cv
    #
    cN
    cfv
    #
    wcel
    #
    vr
    @25
    wral
    @31
    @18
    @35
    vr
    @25
    @33
    @25
    wcel
    @18
    @33
    cX
    wcel
    #
    @7
    @34
    wcel
    #
    wa
    #
    @35
    @24
    @37
    vq
    @33
    cX
    vq
    vr
    weq
    @23
    @34
    @7
    @22
    @33
    cN
    fveq2
    eleq2d
    elrab
    @18
    @38
    wa
    #
    vb
    cv
    #
    @25
    wss
    #
    @35
    vb
    @34
    @39
    @40
    @34
    wcel
    #
    wa
    #
    @41
    wa
    wph
    @36
    @41
    @42
    @35
    wph
    @5
    @8
    @38
    @42
    @41
    simp-5l
    @18
    @38
    @42
    @41
    @36
    @36
    @37
    @42
    @41
    @18
    simpr1l
    3anassrs
    @43
    @41
    simpr
    @39
    @42
    @41
    simplr
    wph
    @36
    wa
    #
    @41
    @42
    w3a
    @29
    @35
    @32
    @44
    @41
    @29
    @42
    @35
    @44
    va
    cv
    #
    @25
    wss
    #
    @29
    w3a
    #
    @45
    @34
    wcel
    #
    wa
    #
    @35
    wi
    #
    @44
    @41
    @29
    w3a
    #
    @42
    wa
    #
    @35
    wi
    va
    vb
    va
    vb
    weq
    #
    @49
    @52
    @35
    @53
    @47
    @51
    @48
    @42
    @53
    @46
    @41
    @44
    @29
    @45
    @40
    @25
    sseq1
    3anbi2d
    @45
    @40
    @34
    eleq1
    anbi12d
    imbi1d
    wph
    @49
    @35
    wph
    @36
    @46
    @29
    @48
    simpl1l
    wph
    cX
    cvv
    wcel
    @25
    cvv
    wcel
    @50
    wph
    cX
    @9
    cvv
    @20
    wph
    cJ
    ctop
    wcel
    #
    @9
    cvv
    wcel
    wph
    cJ
    cN
    cX
    vq
    vp
    va
    vb
    neiptop.o
    neiptop.0
    neiptop.1
    neiptop.2
    neiptop.3
    neiptop.4
    neiptop.5
    neiptoptop
    #
    cJ
    ctop
    uniexg
    syl
    eqeltrd
    @24
    vq
    cX
    cvv
    rabexg
    @44
    @45
    @40
    wss
    #
    @40
    cX
    wss
    #
    w3a
    #
    @48
    wa
    #
    @42
    wi
    #
    @50
    vb
    @25
    cvv
    @40
    @25
    wceq
    #
    @59
    @49
    @42
    @35
    @61
    @58
    @47
    @48
    @61
    @56
    @46
    @57
    @29
    @44
    @40
    @25
    @45
    sseq2
    @40
    @25
    cX
    sseq1
    3anbi23d
    anbi1d
    @40
    @25
    @34
    eleq1
    imbi12d
    @6
    @56
    @57
    w3a
    #
    @45
    @1
    wcel
    #
    wa
    #
    @40
    @1
    wcel
    #
    wi
    #
    @60
    vp
    vr
    vp
    vr
    weq
    #
    @64
    @59
    @65
    @42
    @67
    @62
    @58
    @63
    @48
    @67
    @6
    @44
    @56
    @57
    @67
    @5
    @36
    wph
    @0
    @33
    cX
    eleq1
    anbi2d
    #
    3anbi1d
    @67
    @1
    @34
    @45
    @0
    @33
    cN
    fveq2
    #
    eleq2d
    anbi12d
    @67
    @1
    @34
    @40
    @69
    eleq2d
    imbi12d
    neiptop.1
    chvarv
    vtoclg
    3syl
    mpcom
    chvarv
    3an1rs
    mpan2
    syl211anc
    @39
    wph
    @36
    @37
    @41
    vb
    @34
    wrex
    #
    wph
    @5
    @8
    @38
    simplll
    @18
    @36
    @37
    simprl
    @18
    @36
    @37
    simprr
    @44
    @37
    wa
    #
    vs
    cv
    #
    @25
    wcel
    #
    vs
    @40
    wral
    #
    vb
    @34
    wrex
    #
    @70
    @71
    @72
    cX
    wcel
    #
    @7
    @72
    cN
    cfv
    #
    wcel
    #
    wa
    #
    vs
    @40
    wral
    #
    vb
    @34
    wrex
    #
    @75
    @71
    @78
    vs
    @40
    wral
    #
    vb
    @34
    wrex
    #
    @81
    @18
    @24
    vq
    @40
    wral
    #
    vb
    @1
    wrex
    #
    wi
    #
    @71
    @83
    wi
    vp
    vr
    @67
    @18
    @71
    @85
    @83
    @67
    @6
    @44
    @8
    @37
    @68
    @67
    @1
    @34
    @7
    @69
    eleq2d
    anbi12d
    @67
    @84
    @82
    vb
    @1
    @34
    @69
    @84
    @82
    wb
    @67
    @24
    @78
    vq
    vs
    @40
    vq
    vs
    weq
    @23
    @77
    @7
    @22
    @72
    cN
    fveq2
    eleq2d
    #
    cbvralv
    a1i
    rexeqbidv
    imbi12d
    @6
    @63
    wa
    #
    @45
    @23
    wcel
    #
    vq
    @40
    wral
    vb
    @1
    wrex
    #
    wi
    @86
    va
    vc
    va
    vc
    weq
    #
    @88
    @18
    @90
    @85
    @91
    @63
    @8
    @6
    @45
    @7
    @1
    eleq1
    anbi2d
    #
    @91
    @89
    @24
    vb
    vq
    @1
    @40
    @45
    @7
    @23
    eleq1
    rexralbidv
    imbi12d
    neiptop.4
    chvarv
    chvarv
    @44
    @83
    @81
    wi
    @37
    @44
    @82
    @80
    vb
    @34
    @44
    @42
    wa
    #
    @78
    @79
    vs
    @40
    @93
    vs
    vb
    wel
    wa
    #
    @78
    @76
    @94
    @76
    @78
    @93
    @40
    cX
    @72
    @93
    @40
    cX
    @44
    @34
    @3
    @40
    @44
    @34
    @3
    wph
    cX
    @4
    @33
    cN
    neiptop.0
    ffvelrnda
    elpwid
    sselda
    elpwid
    sselda
    a1d
    ancrd
    ralimdva
    reximdva
    adantr
    mpd
    @74
    @80
    vb
    @34
    @73
    @79
    vs
    @40
    @24
    @78
    vq
    @72
    cX
    @87
    elrab
    ralbii
    rexbii
    sylibr
    @74
    @41
    vb
    @34
    @41
    @74
    vs
    @40
    @25
    dfss3
    biimpri
    reximi
    syl
    syl21anc
    r19.29a
    sylan2b
    ralrimiva
    @30
    @35
    vp
    vr
    @25
    @67
    @1
    @34
    @25
    @69
    eleq2d
    cbvralv
    sylibr
    @25
    cJ
    cN
    cX
    vp
    va
    neiptop.o
    neipeltop
    sylanbrc
    @18
    @5
    @8
    wa
    @27
    @6
    @5
    @8
    wph
    @5
    simpr
    #
    anim1i
    @24
    @8
    vq
    @0
    cX
    vq
    vp
    weq
    @23
    @1
    @7
    @22
    @0
    cN
    fveq2
    eleq2d
    elrab
    sylibr
    @18
    vq
    @25
    @7
    @18
    vq
    nfv
    @24
    vq
    cX
    nfrab1
    vq
    @7
    nfcv
    @22
    @25
    wcel
    @22
    cX
    wcel
    #
    @24
    wa
    #
    @18
    vq
    vc
    wel
    #
    @24
    vq
    cX
    rabid
    @18
    @97
    @98
    @18
    @97
    wa
    wph
    @96
    @24
    @98
    wph
    @5
    @8
    @97
    simplll
    @18
    @96
    @24
    simprl
    @18
    @96
    @24
    simprr
    @18
    vp
    vc
    wel
    #
    wi
    #
    wph
    @96
    wa
    #
    @24
    wa
    #
    @98
    wi
    vp
    vq
    vp
    vq
    weq
    #
    @18
    @102
    @99
    @98
    @103
    @6
    @101
    @8
    @24
    @103
    @5
    @96
    wph
    @0
    @22
    cX
    eleq1
    anbi2d
    @103
    @1
    @23
    @7
    @0
    @22
    cN
    fveq2
    eleq2d
    anbi12d
    vp
    vq
    vc
    elequ1
    imbi12d
    @88
    vp
    va
    wel
    #
    wi
    @100
    va
    vc
    @91
    @88
    @18
    @104
    @99
    @92
    va
    vc
    vp
    elequ2
    imbi12d
    neiptop.3
    chvarv
    chvarv
    syl21anc
    ex
    syl5bi
    ssrd
    @14
    @27
    @28
    wa
    vd
    @25
    cJ
    @12
    @25
    wceq
    @11
    @27
    @13
    @28
    @12
    @25
    @0
    eleq2
    @12
    @25
    @7
    sseq1
    anbi12d
    rspcev
    syl12anc
    jca
    @6
    @16
    wa
    #
    @13
    @8
    vd
    @1
    @6
    @16
    vd
    @6
    vd
    nfv
    @10
    @15
    vd
    @10
    vd
    nfv
    @14
    vd
    cJ
    nfre1
    nfan
    nfan
    @105
    @12
    @1
    wcel
    #
    wa
    #
    @13
    wa
    #
    @6
    @13
    @7
    cX
    wss
    #
    @106
    @8
    @6
    @16
    @106
    @13
    simplll
    #
    @107
    @13
    simpr
    @108
    @7
    @9
    cX
    @6
    @16
    @106
    @13
    @10
    @10
    @15
    @106
    @13
    @6
    simpr1l
    3anassrs
    @108
    @6
    @19
    @110
    @21
    syl
    sseqtr4d
    @105
    @106
    @13
    simplr
    @6
    @45
    @7
    wss
    #
    @109
    w3a
    #
    @63
    wa
    #
    @8
    wi
    #
    @6
    @13
    @109
    w3a
    #
    @106
    wa
    #
    @8
    wi
    va
    vd
    va
    vd
    weq
    #
    @113
    @116
    @8
    @117
    @112
    @115
    @63
    @106
    @117
    @111
    @13
    @6
    @109
    @45
    @12
    @7
    sseq1
    3anbi2d
    @45
    @12
    @1
    eleq1
    anbi12d
    imbi1d
    @66
    @114
    vb
    vc
    vb
    vc
    weq
    #
    @64
    @113
    @65
    @8
    @118
    @62
    @112
    @63
    @118
    @56
    @111
    @57
    @109
    @6
    @40
    @7
    @45
    sseq2
    @40
    @7
    cX
    sseq1
    3anbi23d
    anbi1d
    @40
    @7
    @1
    eleq1
    imbi12d
    neiptop.1
    chvarv
    chvarv
    syl31anc
    @15
    @13
    vd
    @1
    wrex
    @6
    @10
    @14
    @13
    vd
    cJ
    @1
    @12
    cJ
    wcel
    #
    @11
    @13
    @106
    @13
    wa
    @119
    @11
    wa
    @106
    @13
    @119
    @106
    vp
    @12
    @119
    @12
    cX
    wss
    @106
    vp
    @12
    wral
    @12
    cJ
    cN
    cX
    vp
    va
    neiptop.o
    neipeltop
    simprbi
    r19.21bi
    anim1i
    anasss
    reximi2
    ad2antll
    r19.29af
    impbida
    @6
    @54
    @0
    @9
    wcel
    @17
    @16
    wb
    wph
    @54
    @5
    @55
    adantr
    @6
    @0
    cX
    @9
    @95
    @21
    eleqtrd
    @0
    vd
    cJ
    @7
    @9
    @9
    eqid
    isneip
    syl2anc
    bitr4d
    eqrdv
    mpteq2dva
    eqtrd
end
