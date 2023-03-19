include "c7.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cgbo.mm"
include "wcel.mm"
include "wi.mm"
include "codd.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cprime.mm"
include "wrex.mm"
include "simprl.mm"
include "cc0.mm"
include "cfv.mm"
include "cico.mm"
include "c1.mm"
include "cfzo.mm"
include "ciccp.mm"
include "wral.mm"
include "cn.mm"
include "c3.mm"
include "cuz.mm"
include "eluzge3nn.mm"
include "syl.mm"
include "iccelpart.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "cxr.mm"
include "cle.mm"
include "oddz.mm"
include "zred.mm"
include "rexrd.mm"
include "ad2antrl.mm"
include "cr.mm"
include "7re.mm"
include "ltle.mm"
include "sylancr.mm"
include "com12.mm"
include "adantr.mm"
include "impcom.mm"
include "adantl.mm"
include "cdc.mm"
include "eluzelre.mm"
include "simprrr.mm"
include "xrlttrd.mm"
include "wb.mm"
include "oveq1d.mm"
include "rexri.mm"
include "elico1.mm"
include "bitrd.mm"
include "mpbir3and.mm"
include "csn.mm"
include "wo.mm"
include "cun.mm"
include "fzo0sn0fzo1.mm"
include "elun.mm"
include "syl6bb.mm"
include "velsn.mm"
include "fveq2.mm"
include "oveq1.mm"
include "0p1e1.mm"
include "syl6eq.mm"
include "fveq2d.mm"
include "sylan9eq.mm"
include "simprrl.mm"
include "simpr.mm"
include "bgoldbtbndlem1.mm"
include "syl3anc.mm"
include "isgbo.mm"
include "sylib.mm"
include "simprd.mm"
include "ex.mm"
include "sylbid.mm"
include "sylbi.mm"
include "c2.mm"
include "cdif.mm"
include "cmin.mm"
include "c4.mm"
include "fzo0ss1.mm"
include "sseli.mm"
include "eleq1d.mm"
include "breq1d.mm"
include "breq2d.mm"
include "3anbi123d.mm"
include "mpan9.mm"
include "bgoldbtbndlem4.mm"
include "ad2ant2r.mm"
include "expcomd.mm"
include "ceven.mm"
include "simplll.mm"
include "simpllr.mm"
include "eqid.mm"
include "bgoldbtbndlem3.mm"
include "cgbe.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "eleq1.mm"
include "cbvralv.mm"
include "syl5bi.mm"
include "pm3.35.mm"
include "isgbe.mm"
include "eldifi.mm"
include "3ad2ant1.mm"
include "ad5antlr.mm"
include "3anbi3d.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "oddprmALTV.mm"
include "ad4antlr.mm"
include "3simpa.mm"
include "anim12ci.mm"
include "df-3an.mm"
include "sylibr.mm"
include "cc.mm"
include "zcnd.mm"
include "prmz.mm"
include "ad2antlr.mm"
include "npcand.mm"
include "sylan9req.mm"
include "exp31.mm"
include "com23.mm"
include "3impia.mm"
include "jca.mm"
include "rspcedvd.mm"
include "reximdva.mm"
include "exp41.mm"
include "com25.mm"
include "imp.mm"
include "a1d.mm"
include "ancoms.mm"
include "com13.mm"
include "syld.mm"
include "3impib.mm"
include "com15.mm"
include "mpd.mm"
include "impl.mm"
include "resubcld.mm"
include "4re.mm"
include "lelttric.mm"
include "sylancl.mm"
include "mpjaod.mm"
include "mpdan.mm"
include "expcom.mm"
include "impd.mm"
include "jaoi.mm"
include "rexlimdv.mm"
include "embantd.mm"
include "exp32.mm"
include "ralrimiv.mm"

theorem bgoldbtbnd
  let wph: wff ph
  let cD: class D
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cM: class M
  let cN: class N
  let cI: class I
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vm: setvar m
  let cX: class X
  let vf: setvar f
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume bgoldbtbnd.m: |- ( ph -> M e. ( ZZ>= ` ; 1 1 ) )
  assume bgoldbtbnd.n: |- ( ph -> N e. ( ZZ>= ` ; 1 1 ) )
  assume bgoldbtbnd.b: |- ( ph -> A. n e. Even ( ( 4 < n /\ n < N ) -> n e. GoldbachEven ) )
  assume bgoldbtbnd.d: |- ( ph -> D e. ( ZZ>= ` 3 ) )
  assume bgoldbtbnd.f: |- ( ph -> F e. ( RePart ` D ) )
  assume bgoldbtbnd.i: |- ( ph -> A. i e. ( 0 ..^ D ) ( ( F ` i ) e. ( Prime \ { 2 } ) /\ ( ( F ` ( i + 1 ) ) - ( F ` i ) ) < ( N - 4 ) /\ 4 < ( ( F ` ( i + 1 ) ) - ( F ` i ) ) ) )
  assume bgoldbtbnd.0: |- ( ph -> ( F ` 0 ) = 7 )
  assume bgoldbtbnd.1: |- ( ph -> ( F ` 1 ) = ; 1 3 )
  assume bgoldbtbnd.l: |- ( ph -> M < ( F ` D ) )
  assume bgoldbtbnd.r: |- ( ph -> ( F ` D ) e. RR )

  disjoint D i
  disjoint F i
  disjoint N i
  disjoint N n
  disjoint i n
  disjoint n ph
  disjoint I i
  disjoint D p
  disjoint D q
  disjoint D r
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint F m
  disjoint F p
  disjoint F q
  disjoint F r
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint I m
  disjoint I p
  disjoint I q
  disjoint I r
  disjoint N m
  disjoint m n
  disjoint X m
  disjoint X p
  disjoint X q
  disjoint X r
  disjoint p ph
  disjoint ph q
  disjoint ph r
  disjoint D f
  disjoint D j
  disjoint f i
  disjoint f j
  disjoint i j
  disjoint F f
  disjoint F j
  disjoint f m
  disjoint i m
  disjoint j m
  disjoint M j
  disjoint M p
  disjoint M q
  disjoint M r
  disjoint j p
  disjoint j q
  disjoint j r
  disjoint N p
  disjoint N q
  disjoint N r
  disjoint j ph
  disjoint j n
  disjoint n p
  disjoint n q
  disjoint n r
  disjoint f n
  disjoint k x
  assert |- ( ph -> A. n e. Odd ( ( 7 < n /\ n < M ) -> n e. GoldbachOdd ) )

  proof
    wph
    c7
    vn
    cv
    #
    clt
    wbr
    #
    @0
    cM
    clt
    wbr
    #
    wa
    #
    @0
    cgbo
    wcel
    #
    wi
    vn
    codd
    wph
    @0
    codd
    wcel
    #
    @3
    @4
    wph
    @5
    @3
    wa
    #
    wa
    #
    @5
    vp
    cv
    #
    codd
    wcel
    #
    vq
    cv
    #
    codd
    wcel
    #
    vr
    cv
    #
    codd
    wcel
    #
    w3a
    #
    @0
    @8
    @10
    caddc
    co
    #
    @12
    caddc
    co
    #
    wceq
    #
    wa
    #
    vr
    cprime
    wrex
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    wa
    #
    @4
    @7
    @5
    @21
    wph
    @5
    @3
    simprl
    #
    wph
    @6
    @21
    wph
    @0
    cc0
    vf
    cv
    #
    cfv
    #
    cD
    @24
    cfv
    #
    cico
    co
    #
    wcel
    #
    @0
    vj
    cv
    #
    @24
    cfv
    #
    @29
    c1
    caddc
    co
    #
    @24
    cfv
    #
    cico
    co
    #
    wcel
    #
    vj
    cc0
    cD
    cfzo
    co
    #
    wrex
    #
    wi
    #
    vf
    cD
    ciccp
    cfv
    #
    wral
    #
    @6
    @21
    wi
    #
    wph
    cD
    cn
    wcel
    #
    @39
    wph
    cD
    c3
    cuz
    cfv
    wcel
    @41
    bgoldbtbnd.d
    cD
    eluzge3nn
    syl
    #
    vj
    cD
    @0
    vf
    iccelpart
    syl
    wph
    @39
    @0
    cc0
    cF
    cfv
    #
    cD
    cF
    cfv
    #
    cico
    co
    #
    wcel
    #
    @0
    @29
    cF
    cfv
    #
    @31
    cF
    cfv
    #
    cico
    co
    #
    wcel
    #
    vj
    @35
    wrex
    #
    wi
    #
    @40
    wph
    cF
    @38
    wcel
    @39
    @52
    wi
    bgoldbtbnd.f
    @37
    @52
    vf
    cF
    @38
    @24
    cF
    wceq
    #
    @28
    @46
    @36
    @51
    @53
    @27
    @45
    @0
    @53
    @25
    @43
    @26
    @44
    cico
    cc0
    @24
    cF
    fveq1
    cD
    @24
    cF
    fveq1
    oveq12d
    eleq2d
    @53
    @34
    @50
    vj
    @35
    @53
    @33
    @49
    @0
    @53
    @30
    @47
    @32
    @48
    cico
    @29
    @24
    cF
    fveq1
    @31
    @24
    cF
    fveq1
    oveq12d
    eleq2d
    rexbidv
    imbi12d
    rspcv
    syl
    wph
    @6
    @52
    @21
    wph
    @6
    @52
    @21
    wi
    @7
    @46
    @51
    @21
    @7
    @46
    @0
    cxr
    wcel
    #
    c7
    @0
    cle
    wbr
    #
    @0
    @44
    clt
    wbr
    #
    @5
    @54
    wph
    @3
    @5
    @0
    @5
    @0
    @0
    oddz
    #
    zred
    #
    rexrd
    ad2antrl
    #
    @6
    @55
    wph
    @3
    @5
    @55
    @1
    @5
    @55
    wi
    @2
    @5
    @1
    @55
    @5
    c7
    cr
    wcel
    @0
    cr
    wcel
    #
    @1
    @55
    wi
    7re
    @58
    c7
    @0
    ltle
    sylancr
    com12
    adantr
    impcom
    adantl
    @7
    @0
    cM
    @44
    @59
    wph
    cM
    cxr
    wcel
    #
    @6
    wph
    cM
    c1
    c1
    cdc
    #
    cuz
    cfv
    wcel
    #
    @61
    bgoldbtbnd.m
    @63
    cM
    @62
    cM
    eluzelre
    rexrd
    syl
    adantr
    wph
    @44
    cxr
    wcel
    #
    @6
    wph
    @44
    bgoldbtbnd.r
    rexrd
    adantr
    #
    wph
    @5
    @1
    @2
    simprrr
    wph
    cM
    @44
    clt
    wbr
    @6
    bgoldbtbnd.l
    adantr
    xrlttrd
    @7
    @46
    @0
    c7
    @44
    cico
    co
    #
    wcel
    #
    @54
    @55
    @56
    w3a
    #
    wph
    @46
    @67
    wb
    @6
    wph
    @45
    @66
    @0
    wph
    @43
    c7
    @44
    cico
    bgoldbtbnd.0
    oveq1d
    eleq2d
    adantr
    @7
    c7
    cxr
    wcel
    @64
    @67
    @68
    wb
    c7
    7re
    rexri
    @65
    c7
    @44
    @0
    elico1
    sylancr
    bitrd
    mpbir3and
    @7
    @50
    @21
    vj
    @35
    @7
    @29
    @35
    wcel
    #
    @29
    cc0
    csn
    #
    wcel
    #
    @29
    c1
    cD
    cfzo
    co
    #
    wcel
    #
    wo
    #
    @50
    @21
    wi
    #
    wph
    @69
    @74
    wb
    #
    @6
    wph
    @41
    @76
    @42
    @41
    @69
    @29
    @70
    @72
    cun
    #
    wcel
    @74
    @41
    @35
    @77
    @29
    cD
    fzo0sn0fzo1
    eleq2d
    @29
    @70
    @72
    elun
    syl6bb
    syl
    adantr
    @74
    @7
    @75
    @71
    @7
    @75
    wi
    #
    @73
    @71
    @29
    cc0
    wceq
    #
    @78
    vj
    cc0
    velsn
    @79
    @7
    @75
    @79
    @7
    wa
    #
    @50
    @0
    c7
    c1
    c3
    cdc
    #
    cico
    co
    #
    wcel
    #
    @21
    @80
    @49
    @82
    @0
    @79
    @7
    @49
    @43
    c1
    cF
    cfv
    #
    cico
    co
    #
    @82
    @79
    @47
    @43
    @48
    @84
    cico
    @29
    cc0
    cF
    fveq2
    @79
    @31
    c1
    cF
    @79
    @31
    cc0
    c1
    caddc
    co
    c1
    @29
    cc0
    c1
    caddc
    oveq1
    0p1e1
    syl6eq
    fveq2d
    oveq12d
    wph
    @85
    @82
    wceq
    @6
    wph
    @43
    c7
    @84
    @81
    cico
    bgoldbtbnd.0
    bgoldbtbnd.1
    oveq12d
    adantr
    sylan9eq
    eleq2d
    @7
    @83
    @21
    wi
    @79
    @7
    @83
    @21
    @7
    @83
    wa
    #
    @5
    @21
    @86
    @4
    @22
    @86
    @5
    @1
    @83
    @4
    @7
    @5
    @83
    @23
    adantr
    @7
    @1
    @83
    wph
    @5
    @1
    @2
    simprrl
    adantr
    @7
    @83
    simpr
    @0
    bgoldbtbndlem1
    syl3anc
    @0
    vr
    vq
    vp
    isgbo
    #
    sylib
    simprd
    ex
    adantl
    sylbid
    ex
    sylbi
    @73
    wph
    @6
    @75
    wph
    @73
    @6
    @75
    wi
    #
    wph
    @73
    wa
    #
    @47
    cprime
    c2
    csn
    #
    cdif
    #
    wcel
    #
    @48
    @47
    cmin
    co
    #
    cN
    c4
    cmin
    co
    #
    clt
    wbr
    #
    c4
    @93
    clt
    wbr
    #
    w3a
    #
    @88
    wph
    vi
    cv
    #
    cF
    cfv
    #
    @91
    wcel
    #
    @98
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @99
    cmin
    co
    #
    @94
    clt
    wbr
    #
    c4
    @103
    clt
    wbr
    #
    w3a
    #
    vi
    @35
    wral
    #
    @73
    @97
    bgoldbtbnd.i
    @73
    @69
    @107
    @97
    wi
    @72
    @35
    @29
    cD
    fzo0ss1
    sseli
    @106
    @97
    vi
    @29
    @35
    @98
    @29
    wceq
    #
    @100
    @92
    @104
    @95
    @105
    @96
    @108
    @99
    @47
    @91
    @98
    @29
    cF
    fveq2
    #
    eleq1d
    @108
    @103
    @93
    @94
    clt
    @108
    @102
    @48
    @99
    @47
    cmin
    @108
    @101
    @31
    cF
    @98
    @29
    c1
    caddc
    oveq1
    fveq2d
    @109
    oveq12d
    #
    breq1d
    @108
    @103
    @93
    c4
    clt
    @110
    breq2d
    3anbi123d
    rspcv
    syl
    mpan9
    @89
    @97
    wa
    #
    @6
    @75
    @111
    @6
    wa
    #
    @0
    @47
    cmin
    co
    #
    c4
    cle
    wbr
    #
    @75
    c4
    @113
    clt
    wbr
    #
    @112
    @50
    @114
    @21
    @89
    @5
    @50
    @114
    wa
    @21
    wi
    @97
    @3
    wph
    cD
    vi
    vn
    cF
    @29
    cM
    cN
    @0
    vr
    vq
    vp
    bgoldbtbnd.m
    bgoldbtbnd.n
    bgoldbtbnd.b
    bgoldbtbnd.d
    bgoldbtbnd.f
    bgoldbtbnd.i
    bgoldbtbnd.0
    bgoldbtbnd.1
    bgoldbtbnd.l
    bgoldbtbnd.r
    bgoldbtbndlem4
    ad2ant2r
    expcomd
    @112
    @50
    @115
    @21
    @112
    @50
    @115
    wa
    #
    @113
    ceven
    wcel
    #
    @113
    cN
    clt
    wbr
    #
    @115
    w3a
    #
    @21
    @112
    wph
    @5
    @73
    @116
    @119
    wi
    wph
    @73
    @97
    @6
    simplll
    @111
    @5
    @3
    simprl
    wph
    @73
    @97
    @6
    simpllr
    wph
    cD
    @113
    vi
    vn
    cF
    @29
    cM
    cN
    @0
    bgoldbtbnd.m
    bgoldbtbnd.n
    bgoldbtbnd.b
    bgoldbtbnd.d
    bgoldbtbnd.f
    bgoldbtbnd.i
    bgoldbtbnd.0
    bgoldbtbnd.1
    bgoldbtbnd.l
    bgoldbtbnd.r
    @113
    eqid
    bgoldbtbndlem3
    syl3anc
    @111
    @6
    @119
    @21
    wi
    #
    wph
    @73
    @97
    @6
    @120
    wi
    #
    wph
    c4
    @0
    clt
    wbr
    #
    @0
    cN
    clt
    wbr
    #
    wa
    #
    @0
    cgbe
    wcel
    #
    wi
    #
    vn
    ceven
    wral
    #
    @73
    @97
    wa
    #
    @121
    wi
    bgoldbtbnd.b
    @119
    @127
    @128
    @6
    wph
    @21
    @117
    @118
    @115
    @127
    @128
    @6
    wph
    @21
    wi
    wi
    wi
    #
    wi
    @117
    @127
    @118
    @115
    wa
    #
    @129
    @117
    @127
    @115
    @118
    wa
    #
    @113
    cgbe
    wcel
    #
    wi
    #
    @130
    @129
    wi
    @127
    c4
    vm
    cv
    #
    clt
    wbr
    #
    @134
    cN
    clt
    wbr
    #
    wa
    #
    @134
    cgbe
    wcel
    #
    wi
    #
    vm
    ceven
    wral
    @117
    @133
    @126
    @139
    vn
    vm
    ceven
    @0
    @134
    wceq
    #
    @124
    @137
    @125
    @138
    @140
    @122
    @135
    @123
    @136
    @0
    @134
    c4
    clt
    breq2
    @0
    @134
    cN
    clt
    breq1
    anbi12d
    @0
    @134
    cgbe
    eleq1
    imbi12d
    cbvralv
    @139
    @133
    vm
    @113
    ceven
    @134
    @113
    wceq
    #
    @137
    @131
    @138
    @132
    @141
    @135
    @115
    @136
    @118
    @134
    @113
    c4
    clt
    breq2
    @134
    @113
    cN
    clt
    breq1
    anbi12d
    @134
    @113
    cgbe
    eleq1
    imbi12d
    rspcv
    syl5bi
    @130
    @133
    @117
    @129
    @115
    @118
    @133
    @117
    @129
    wi
    #
    wi
    @131
    @133
    @142
    @131
    @133
    wa
    @132
    @142
    @131
    @132
    pm3.35
    @132
    @129
    @117
    @132
    @117
    @9
    @11
    @113
    @15
    wceq
    #
    w3a
    #
    vq
    cprime
    wrex
    #
    vp
    cprime
    wrex
    #
    wa
    @129
    @113
    vq
    vp
    isgbe
    @117
    @146
    @129
    @117
    wph
    @128
    @6
    @146
    @21
    @117
    wph
    @128
    @6
    @146
    @21
    wi
    @117
    wph
    wa
    #
    @128
    wa
    #
    @6
    wa
    #
    @145
    @20
    vp
    cprime
    @149
    @8
    cprime
    wcel
    #
    wa
    #
    @144
    @19
    vq
    cprime
    @151
    @10
    cprime
    wcel
    #
    wa
    #
    @144
    @19
    @153
    @144
    wa
    #
    @18
    @9
    @11
    @47
    codd
    wcel
    #
    w3a
    #
    @0
    @15
    @47
    caddc
    co
    #
    wceq
    #
    wa
    #
    vr
    @47
    cprime
    @128
    @47
    cprime
    wcel
    #
    @147
    @6
    @150
    @152
    @144
    @97
    @160
    @73
    @92
    @95
    @160
    @96
    @47
    cprime
    @90
    eldifi
    #
    3ad2ant1
    adantl
    ad5antlr
    @12
    @47
    wceq
    #
    @18
    @159
    wb
    @154
    @162
    @14
    @156
    @17
    @158
    @162
    @13
    @155
    @9
    @11
    @12
    @47
    codd
    eleq1
    3anbi3d
    @162
    @16
    @157
    @0
    @12
    @47
    @15
    caddc
    oveq2
    eqeq2d
    anbi12d
    adantl
    @154
    @156
    @158
    @154
    @9
    @11
    wa
    #
    @155
    wa
    @156
    @153
    @155
    @144
    @163
    @128
    @155
    @147
    @6
    @150
    @152
    @97
    @155
    @73
    @92
    @95
    @155
    @96
    @47
    oddprmALTV
    3ad2ant1
    adantl
    ad4antlr
    @9
    @11
    @143
    3simpa
    anim12ci
    @9
    @11
    @155
    df-3an
    sylibr
    @144
    @153
    @158
    @9
    @11
    @143
    @153
    @158
    wi
    @163
    @153
    @143
    @158
    @163
    @153
    @143
    @158
    @163
    @153
    wa
    @143
    @0
    @113
    @47
    caddc
    co
    #
    @157
    @151
    @164
    @0
    wceq
    #
    @163
    @152
    @149
    @165
    @150
    @149
    @0
    @47
    @5
    @0
    cc
    wcel
    @148
    @3
    @5
    @0
    @57
    zcnd
    ad2antrl
    @128
    @47
    cc
    wcel
    #
    @147
    @6
    @97
    @166
    @73
    @92
    @95
    @166
    @96
    @92
    @160
    @166
    @161
    @160
    @47
    @47
    prmz
    #
    zcnd
    syl
    3ad2ant1
    adantl
    ad2antlr
    npcand
    adantr
    ad2antrl
    @113
    @15
    @47
    caddc
    oveq1
    sylan9req
    exp31
    com23
    3impia
    impcom
    jca
    rspcedvd
    ex
    reximdva
    reximdva
    exp41
    com25
    imp
    sylbi
    a1d
    syl
    ex
    ancoms
    com13
    syld
    com23
    3impib
    com15
    mpd
    impl
    imp
    syld
    expcomd
    @112
    @113
    cr
    wcel
    c4
    cr
    wcel
    @114
    @115
    wo
    @112
    @0
    @47
    @5
    @60
    @111
    @3
    @58
    ad2antrl
    @97
    @47
    cr
    wcel
    #
    @89
    @6
    @92
    @95
    @168
    @96
    @92
    @160
    @168
    @161
    @160
    @47
    @167
    zred
    syl
    3ad2ant1
    ad2antlr
    resubcld
    4re
    @113
    c4
    lelttric
    sylancl
    mpjaod
    ex
    mpdan
    expcom
    impd
    jaoi
    com12
    sylbid
    rexlimdv
    embantd
    ex
    com23
    syld
    mpd
    imp
    jca
    @87
    sylibr
    exp32
    ralrimiv
end
