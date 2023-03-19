include "com.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "cfv.mm"
include "wf1.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "wb.mm"
include "fveq2.mm"
include "f1eq1.mm"
include "syl.mm"
include "oveq2.mm"
include "f1eq2.mm"
include "bitrd.mm"
include "imbi2d.mm"
include "c0.mm"
include "cop.mm"
include "csn.mm"
include "csuc.mm"
include "cvv.mm"
include "snex.mm"
include "cres.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "seqom0g.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "weq.mm"
include "wss.mm"
include "wf1o.mm"
include "0ex.mm"
include "f1osng.mm"
include "sylancr.mm"
include "f1of1.mm"
include "snssd.mm"
include "f1ss.mm"
include "syl2anc.mm"
include "c1o.mm"
include "map0e.mm"
include "df1o2.mm"
include "mpbird.mm"
include "wa.mm"
include "wf.mm"
include "wral.mm"
include "cxp.mm"
include "ad2antrr.mm"
include "f1of.mm"
include "f1f.mm"
include "ad2antll.mm"
include "adantr.mm"
include "elmapi.mm"
include "adantl.mm"
include "sssucid.mm"
include "fssres.mm"
include "sylancl.mm"
include "vex.mm"
include "elmapg.mm"
include "ffvelrnd.mm"
include "sucid.mm"
include "ffvelrn.mm"
include "fovrnd.mm"
include "eqid.mm"
include "fmptd.mm"
include "seqomsuc.mm"
include "ad2antrl.mm"
include "fvex.mm"
include "reseq1.mm"
include "fveq2d.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "suceq.mm"
include "oveq2d.mm"
include "simpr.mm"
include "reseq2.mm"
include "fveq12d.mm"
include "simpl.mm"
include "mpteq12dv.mm"
include "syl5eq.mm"
include "nfcv.mm"
include "cbvmpt2.mm"
include "ovex.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "mp2an.mm"
include "feq1d.mm"
include "wfn.mm"
include "ffn.mm"
include "a1i.mm"
include "fvreseq.mm"
include "syl21anc.mm"
include "eqeq12d.mm"
include "ralsn.mm"
include "bicomi.mm"
include "anbi12d.mm"
include "fveq1d.mm"
include "fvmpt.mm"
include "eqtrd.mm"
include "df-ov.mm"
include "opelxpi.mm"
include "f1fveq.mm"
include "syl12anc.mm"
include "opth.mm"
include "syl6bb.mm"
include "simplrr.mm"
include "anbi1d.mm"
include "3bitrd.mm"
include "eqfnfv.mm"
include "cun.mm"
include "df-suc.mm"
include "raleqi.mm"
include "ralunb.mm"
include "bitri.mm"
include "3bitr4d.mm"
include "biimpd.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "expr.mm"
include "expcom.mm"
include "finds2.mm"
include "vtoclga.mm"
include "impcom.mm"

theorem fseqenlem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vf: setvar f
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cV: class V
  let vy: setvar y
  let va: setvar a
  let vb: setvar b
  let vz: setvar z
  let vk: setvar k
  let vm: setvar m
  let vw: setvar w
  let cK: class K
  assume fseqenlem.a: |- ( ph -> A e. V )
  assume fseqenlem.b: |- ( ph -> B e. A )
  assume fseqenlem.f: |- ( ph -> F : ( A X. A ) -1-1-onto-> A )
  assume fseqenlem.g: |- G = seqom ( ( n e. _V , f e. _V |-> ( x e. ( A ^m suc n ) |-> ( ( f ` ( x |` n ) ) F ( x ` n ) ) ) ) , { <. (/) , B >. } )

  disjoint f n
  disjoint f x
  disjoint F f
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint A f
  disjoint A n
  disjoint A x
  disjoint n ph
  disjoint ph x
  disjoint B y
  disjoint C y
  disjoint a b
  disjoint a f
  disjoint a n
  disjoint a x
  disjoint a z
  disjoint F a
  disjoint b f
  disjoint b n
  disjoint b x
  disjoint b z
  disjoint F b
  disjoint f z
  disjoint n z
  disjoint x z
  disjoint F z
  disjoint a k
  disjoint a m
  disjoint a y
  disjoint G a
  disjoint b k
  disjoint b m
  disjoint b y
  disjoint G b
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint G k
  disjoint m y
  disjoint m z
  disjoint G m
  disjoint y z
  disjoint G y
  disjoint G z
  disjoint w z
  disjoint K w
  disjoint K z
  disjoint A a
  disjoint A b
  disjoint f k
  disjoint f m
  disjoint f y
  disjoint k n
  disjoint k x
  disjoint A k
  disjoint m n
  disjoint m x
  disjoint A m
  disjoint n y
  disjoint x y
  disjoint A y
  disjoint A z
  disjoint a w
  disjoint a ph
  disjoint b w
  disjoint b ph
  disjoint k w
  disjoint k ph
  disjoint m w
  disjoint m ph
  disjoint n w
  disjoint w x
  disjoint w y
  disjoint ph w
  disjoint ph y
  disjoint ph z
  assert |- ( ( ph /\ C e. _om ) -> ( G ` C ) : ( A ^m C ) -1-1-> A )

  proof
    cC
    com
    wcel
    wph
    cA
    cC
    cmap
    co
    #
    cA
    cC
    cG
    cfv
    #
    wf1
    #
    wph
    cA
    vy
    cv
    #
    cmap
    co
    #
    cA
    @3
    cG
    cfv
    #
    wf1
    #
    wi
    wph
    @2
    wi
    vy
    cC
    com
    @3
    cC
    wceq
    #
    @6
    @2
    wph
    @7
    @6
    @4
    cA
    @1
    wf1
    #
    @2
    @7
    @5
    @1
    wceq
    @6
    @8
    wb
    @3
    cC
    cG
    fveq2
    @4
    cA
    @5
    @1
    f1eq1
    syl
    @7
    @4
    @0
    wceq
    @8
    @2
    wb
    @3
    cC
    cA
    cmap
    oveq2
    @4
    @0
    cA
    @1
    f1eq2
    syl
    bitrd
    imbi2d
    @6
    cA
    c0
    cmap
    co
    #
    cA
    c0
    cB
    cop
    #
    csn
    #
    wf1
    #
    cA
    vm
    cv
    #
    cmap
    co
    #
    cA
    @13
    cG
    cfv
    #
    wf1
    #
    cA
    @13
    csuc
    #
    cmap
    co
    #
    cA
    @17
    cG
    cfv
    #
    wf1
    #
    wph
    vy
    vm
    @3
    c0
    wceq
    #
    @6
    @4
    cA
    @11
    wf1
    #
    @12
    @21
    @5
    @11
    wceq
    @6
    @22
    wb
    @21
    @5
    c0
    cG
    cfv
    #
    @11
    @3
    c0
    cG
    fveq2
    @11
    cvv
    wcel
    @23
    @11
    wceq
    @10
    snex
    vn
    vf
    cvv
    cvv
    vx
    cA
    vn
    cv
    #
    csuc
    #
    cmap
    co
    #
    vx
    cv
    #
    @24
    cres
    #
    vf
    cv
    #
    cfv
    #
    @24
    @27
    cfv
    #
    cF
    co
    #
    cmpt
    #
    cmpt2
    #
    cG
    @11
    cvv
    fseqenlem.g
    seqom0g
    ax-mp
    syl6eq
    @4
    cA
    @5
    @11
    f1eq1
    syl
    @21
    @4
    @9
    wceq
    @22
    @12
    wb
    @3
    c0
    cA
    cmap
    oveq2
    @4
    @9
    cA
    @11
    f1eq2
    syl
    bitrd
    vy
    vm
    weq
    #
    @6
    @4
    cA
    @15
    wf1
    #
    @16
    @35
    @5
    @15
    wceq
    @6
    @36
    wb
    @3
    @13
    cG
    fveq2
    @4
    cA
    @5
    @15
    f1eq1
    syl
    @35
    @4
    @14
    wceq
    @36
    @16
    wb
    @3
    @13
    cA
    cmap
    oveq2
    @4
    @14
    cA
    @15
    f1eq2
    syl
    bitrd
    @3
    @17
    wceq
    #
    @6
    @4
    cA
    @19
    wf1
    #
    @20
    @37
    @5
    @19
    wceq
    @6
    @38
    wb
    @3
    @17
    cG
    fveq2
    @4
    cA
    @5
    @19
    f1eq1
    syl
    @37
    @4
    @18
    wceq
    @38
    @20
    wb
    @3
    @17
    cA
    cmap
    oveq2
    @4
    @18
    cA
    @19
    f1eq2
    syl
    bitrd
    wph
    @12
    c0
    csn
    #
    cA
    @11
    wf1
    #
    wph
    @39
    cB
    csn
    #
    @11
    wf1
    #
    @41
    cA
    wss
    @40
    wph
    @39
    @41
    @11
    wf1o
    #
    @42
    wph
    c0
    cvv
    wcel
    cB
    cA
    wcel
    @43
    0ex
    fseqenlem.b
    c0
    cB
    cvv
    cA
    f1osng
    sylancr
    @39
    @41
    @11
    f1of1
    syl
    wph
    cB
    cA
    fseqenlem.b
    snssd
    @39
    @41
    cA
    @11
    f1ss
    syl2anc
    wph
    @9
    @39
    wceq
    @12
    @40
    wb
    wph
    @9
    c1o
    @39
    wph
    cA
    cV
    wcel
    #
    @9
    c1o
    wceq
    fseqenlem.a
    cA
    cV
    map0e
    syl
    df1o2
    syl6eq
    @9
    @39
    cA
    @11
    f1eq2
    syl
    mpbird
    wph
    @13
    com
    wcel
    #
    @16
    @20
    wi
    wph
    @45
    @16
    @20
    wph
    @45
    @16
    wa
    #
    wa
    #
    @18
    cA
    @19
    wf
    #
    va
    cv
    #
    @19
    cfv
    #
    vb
    cv
    #
    @19
    cfv
    #
    wceq
    #
    va
    vb
    weq
    #
    wi
    #
    vb
    @18
    wral
    va
    @18
    wral
    @20
    @47
    @48
    @18
    cA
    vz
    @18
    vz
    cv
    #
    @13
    cres
    #
    @15
    cfv
    #
    @13
    @56
    cfv
    #
    cF
    co
    #
    cmpt
    #
    wf
    @47
    vz
    @18
    @60
    cA
    @61
    @47
    @56
    @18
    wcel
    #
    wa
    #
    @58
    @59
    cA
    cA
    cA
    cF
    @63
    cA
    cA
    cxp
    #
    cA
    cF
    wf1o
    #
    @64
    cA
    cF
    wf
    wph
    @65
    @46
    @62
    fseqenlem.f
    ad2antrr
    @64
    cA
    cF
    f1of
    syl
    @63
    @14
    cA
    @57
    @15
    @47
    @14
    cA
    @15
    wf
    #
    @62
    @16
    @66
    wph
    @45
    @14
    cA
    @15
    f1f
    ad2antll
    #
    adantr
    @63
    @57
    @14
    wcel
    #
    @13
    cA
    @57
    wf
    #
    @63
    @17
    cA
    @56
    wf
    #
    @13
    @17
    wss
    #
    @69
    @62
    @70
    @47
    @56
    cA
    @17
    elmapi
    adantl
    #
    @13
    sssucid
    #
    @17
    cA
    @13
    @56
    fssres
    sylancl
    @63
    @44
    @13
    cvv
    wcel
    #
    @68
    @69
    wb
    wph
    @44
    @46
    @62
    fseqenlem.a
    ad2antrr
    vm
    vex
    #
    cA
    @13
    @57
    cV
    cvv
    elmapg
    sylancl
    mpbird
    ffvelrnd
    @63
    @70
    @13
    @17
    wcel
    #
    @59
    cA
    wcel
    @72
    @13
    @75
    sucid
    #
    @17
    cA
    @13
    @56
    ffvelrn
    sylancl
    fovrnd
    @61
    eqid
    #
    fmptd
    @47
    @18
    cA
    @19
    @61
    @47
    @19
    @13
    @15
    @34
    co
    #
    @61
    @45
    @19
    @79
    wceq
    wph
    @16
    @13
    @34
    cG
    @11
    fseqenlem.g
    seqomsuc
    ad2antrl
    @74
    @15
    cvv
    wcel
    @79
    @61
    wceq
    @75
    @13
    cG
    fvex
    va
    vb
    @13
    @15
    cvv
    cvv
    vx
    cA
    @49
    csuc
    #
    cmap
    co
    #
    @27
    @49
    cres
    #
    @51
    cfv
    #
    @49
    @27
    cfv
    #
    cF
    co
    #
    cmpt
    #
    @61
    @34
    va
    vm
    weq
    #
    @51
    @15
    wceq
    #
    wa
    #
    @86
    vz
    @81
    @56
    @49
    cres
    #
    @51
    cfv
    #
    @49
    @56
    cfv
    #
    cF
    co
    #
    cmpt
    @61
    vx
    vz
    @81
    @85
    @93
    vx
    vz
    weq
    #
    @83
    @91
    @84
    @92
    cF
    @94
    @82
    @90
    @51
    @27
    @56
    @49
    reseq1
    fveq2d
    @49
    @27
    @56
    fveq1
    oveq12d
    cbvmptv
    @89
    vz
    @81
    @93
    @18
    @60
    @89
    @80
    @17
    cA
    cmap
    @87
    @80
    @17
    wceq
    @88
    @49
    @13
    suceq
    adantr
    oveq2d
    @89
    @91
    @58
    @92
    @59
    cF
    @89
    @90
    @57
    @51
    @15
    @87
    @88
    simpr
    @87
    @90
    @57
    wceq
    @88
    @49
    @13
    @56
    reseq2
    adantr
    fveq12d
    @89
    @49
    @13
    @56
    @87
    @88
    simpl
    fveq2d
    oveq12d
    mpteq12dv
    syl5eq
    vn
    vf
    va
    vb
    cvv
    cvv
    @33
    @86
    va
    @33
    nfcv
    vb
    @33
    nfcv
    vn
    @86
    nfcv
    vf
    @86
    nfcv
    vn
    va
    weq
    #
    vf
    vb
    weq
    #
    wa
    #
    vx
    @26
    @32
    @81
    @85
    @97
    @25
    @80
    cA
    cmap
    @95
    @25
    @80
    wceq
    @96
    @24
    @49
    suceq
    adantr
    oveq2d
    @97
    @30
    @83
    @31
    @84
    cF
    @97
    @28
    @82
    @29
    @51
    @95
    @96
    simpr
    @95
    @28
    @82
    wceq
    @96
    @24
    @49
    @27
    reseq2
    adantr
    fveq12d
    @97
    @24
    @49
    @27
    @95
    @96
    simpl
    fveq2d
    oveq12d
    mpteq12dv
    cbvmpt2
    vz
    @18
    @60
    cA
    @17
    cmap
    ovex
    mptex
    ovmpt2a
    mp2an
    syl6eq
    #
    feq1d
    mpbird
    @47
    @55
    va
    vb
    @18
    @18
    @47
    @49
    @18
    wcel
    #
    @51
    @18
    wcel
    #
    wa
    #
    wa
    #
    @53
    @54
    @102
    @49
    @13
    cres
    #
    @51
    @13
    cres
    #
    wceq
    #
    @13
    @49
    cfv
    #
    @13
    @51
    cfv
    #
    wceq
    #
    wa
    #
    @27
    @49
    cfv
    #
    @27
    @51
    cfv
    #
    wceq
    #
    vx
    @13
    wral
    #
    @112
    vx
    @13
    csn
    #
    wral
    #
    wa
    #
    @53
    @54
    @102
    @105
    @113
    @108
    @115
    @102
    @49
    @17
    wfn
    #
    @51
    @17
    wfn
    #
    @71
    @105
    @113
    wb
    @102
    @17
    cA
    @49
    wf
    #
    @117
    @99
    @119
    @47
    @100
    @49
    cA
    @17
    elmapi
    ad2antrl
    #
    @17
    cA
    @49
    ffn
    syl
    #
    @102
    @17
    cA
    @51
    wf
    #
    @118
    @100
    @122
    @47
    @99
    @51
    cA
    @17
    elmapi
    ad2antll
    #
    @17
    cA
    @51
    ffn
    syl
    #
    @71
    @102
    @73
    a1i
    vx
    @17
    @13
    @49
    @51
    fvreseq
    syl21anc
    @108
    @115
    wb
    @102
    @115
    @108
    @112
    @108
    vx
    @13
    @75
    vx
    vm
    weq
    @110
    @106
    @111
    @107
    @27
    @13
    @49
    fveq2
    @27
    @13
    @51
    fveq2
    eqeq12d
    ralsn
    bicomi
    a1i
    anbi12d
    @102
    @53
    @103
    @15
    cfv
    #
    @106
    cop
    #
    cF
    cfv
    #
    @104
    @15
    cfv
    #
    @107
    cop
    #
    cF
    cfv
    #
    wceq
    #
    @125
    @128
    wceq
    #
    @108
    wa
    #
    @109
    @102
    @50
    @127
    @52
    @130
    @102
    @50
    @125
    @106
    cF
    co
    #
    @127
    @102
    @50
    @49
    @61
    cfv
    #
    @134
    @102
    @49
    @19
    @61
    @47
    @19
    @61
    wceq
    @101
    @98
    adantr
    #
    fveq1d
    @99
    @135
    @134
    wceq
    @47
    @100
    vz
    @49
    @60
    @134
    @18
    @61
    vz
    va
    weq
    #
    @58
    @125
    @59
    @106
    cF
    @137
    @57
    @103
    @15
    @56
    @49
    @13
    reseq1
    fveq2d
    @13
    @56
    @49
    fveq1
    oveq12d
    @78
    @125
    @106
    cF
    ovex
    fvmpt
    ad2antrl
    eqtrd
    @125
    @106
    cF
    df-ov
    syl6eq
    @102
    @52
    @128
    @107
    cF
    co
    #
    @130
    @102
    @52
    @51
    @61
    cfv
    #
    @138
    @102
    @51
    @19
    @61
    @136
    fveq1d
    @100
    @139
    @138
    wceq
    @47
    @99
    vz
    @51
    @60
    @138
    @18
    @61
    vz
    vb
    weq
    #
    @58
    @128
    @59
    @107
    cF
    @140
    @57
    @104
    @15
    @56
    @51
    @13
    reseq1
    fveq2d
    @13
    @56
    @51
    fveq1
    oveq12d
    @78
    @128
    @107
    cF
    ovex
    fvmpt
    ad2antll
    eqtrd
    @128
    @107
    cF
    df-ov
    syl6eq
    eqeq12d
    @102
    @131
    @126
    @129
    wceq
    #
    @133
    @102
    @64
    cA
    cF
    wf1
    #
    @126
    @64
    wcel
    #
    @129
    @64
    wcel
    #
    @131
    @141
    wb
    @102
    @65
    @142
    wph
    @65
    @46
    @101
    fseqenlem.f
    ad2antrr
    @64
    cA
    cF
    f1of1
    syl
    @102
    @125
    cA
    wcel
    @106
    cA
    wcel
    #
    @143
    @102
    @14
    cA
    @103
    @15
    @47
    @66
    @101
    @67
    adantr
    #
    @102
    @103
    @14
    wcel
    #
    @13
    cA
    @103
    wf
    #
    @102
    @119
    @71
    @148
    @120
    @73
    @17
    cA
    @13
    @49
    fssres
    sylancl
    @102
    @44
    @74
    @147
    @148
    wb
    wph
    @44
    @46
    @101
    fseqenlem.a
    ad2antrr
    #
    @75
    cA
    @13
    @103
    cV
    cvv
    elmapg
    sylancl
    mpbird
    #
    ffvelrnd
    @102
    @119
    @76
    @145
    @120
    @77
    @17
    cA
    @13
    @49
    ffvelrn
    sylancl
    @125
    @106
    cA
    cA
    opelxpi
    syl2anc
    @102
    @128
    cA
    wcel
    @107
    cA
    wcel
    #
    @144
    @102
    @14
    cA
    @104
    @15
    @146
    @102
    @104
    @14
    wcel
    #
    @13
    cA
    @104
    wf
    #
    @102
    @122
    @71
    @153
    @123
    @73
    @17
    cA
    @13
    @51
    fssres
    sylancl
    @102
    @44
    @74
    @152
    @153
    wb
    @149
    @75
    cA
    @13
    @104
    cV
    cvv
    elmapg
    sylancl
    mpbird
    #
    ffvelrnd
    @102
    @122
    @76
    @151
    @123
    @77
    @17
    cA
    @13
    @51
    ffvelrn
    sylancl
    @128
    @107
    cA
    cA
    opelxpi
    syl2anc
    @64
    cA
    @126
    @129
    cF
    f1fveq
    syl12anc
    @125
    @106
    @128
    @107
    @103
    @15
    fvex
    @13
    @49
    fvex
    opth
    syl6bb
    @102
    @132
    @105
    @108
    @102
    @16
    @147
    @152
    @132
    @105
    wb
    wph
    @45
    @16
    @101
    simplrr
    @150
    @154
    @14
    cA
    @103
    @104
    @15
    f1fveq
    syl12anc
    anbi1d
    3bitrd
    @102
    @54
    @112
    vx
    @17
    wral
    #
    @116
    @102
    @117
    @118
    @54
    @155
    wb
    @121
    @124
    vx
    @17
    @49
    @51
    eqfnfv
    syl2anc
    @155
    @112
    vx
    @13
    @114
    cun
    #
    wral
    @116
    @112
    vx
    @17
    @156
    @13
    df-suc
    raleqi
    @112
    vx
    @13
    @114
    ralunb
    bitri
    syl6bb
    3bitr4d
    biimpd
    ralrimivva
    va
    vb
    @18
    cA
    @19
    dff13
    sylanbrc
    expr
    expcom
    finds2
    vtoclga
    impcom
end
