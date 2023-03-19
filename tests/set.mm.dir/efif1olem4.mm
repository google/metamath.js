include "wf1.mm"
include "wfo.mm"
include "wf1o.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "weq.mm"
include "wi.mm"
include "wral.mm"
include "ci.mm"
include "cmul.mm"
include "co.mm"
include "ce.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "sselda.mm"
include "cabs.mm"
include "ccnv.mm"
include "c1.mm"
include "csn.mm"
include "cima.mm"
include "cc.mm"
include "ax-icn.mm"
include "recn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "efcl.mm"
include "syl.mm"
include "absefi.mm"
include "wfn.mm"
include "wb.mm"
include "absf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "fniniseg.mm"
include "sylanbrc.mm"
include "syl6eleqr.mm"
include "fmptd.mm"
include "wss.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "sseldd.mm"
include "recnd.mm"
include "simplrr.mm"
include "cmin.mm"
include "c2.mm"
include "cpi.mm"
include "cdiv.mm"
include "cc0.mm"
include "subcld.mm"
include "wne.mm"
include "2re.mm"
include "pire.mm"
include "remulcli.mm"
include "recni.mm"
include "2pos.mm"
include "pipos.mm"
include "mulgt0ii.mm"
include "gt0ne0ii.mm"
include "divcl.mm"
include "mp3an23.mm"
include "clt.mm"
include "wbr.mm"
include "absdiv.mm"
include "cle.mm"
include "0re.mm"
include "ltleii.mm"
include "absid.mm"
include "mp2an.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "adantr.mm"
include "mulid1i.mm"
include "syl6breqr.mm"
include "abscld.mm"
include "1re.mm"
include "pm3.2i.mm"
include "ltdivmul.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "cn0.mm"
include "cz.mm"
include "ine0.mm"
include "divcan5.mm"
include "a1i.mm"
include "subdid.mm"
include "fveq2d.mm"
include "efsub.mm"
include "syl2anc.mm"
include "efne0.mm"
include "simpr.mm"
include "oveq2.mm"
include "fvex.mm"
include "fvmpt.mm"
include "3eqtr3d.mm"
include "diveq1bd.mm"
include "3eqtrd.mm"
include "efeq1.mm"
include "mpbid.mm"
include "eqeltrrd.mm"
include "nn0abscl.mm"
include "nn0lt10b.mm"
include "abs00d.mm"
include "diveq0.mm"
include "subeq0d.mm"
include "ex.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "wrex.mm"
include "csqrt.mm"
include "cim.mm"
include "cneg.mm"
include "cicc.mm"
include "neghalfpire.mm"
include "halfpire.mm"
include "iccssre.mm"
include "efif1olem3.mm"
include "csin.mm"
include "cres.mm"
include "resinf1o.mm"
include "f1oeq1.mm"
include "mpbir.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "mp2b.mm"
include "ffvelrni.mm"
include "sseldi.mm"
include "remulcl.mm"
include "ralrimiva.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eleq1d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "caddc.mm"
include "npcand.mm"
include "eqtrd.mm"
include "efadd.mm"
include "cexp.mm"
include "2cn.mm"
include "mul12.mm"
include "mp3an12.mm"
include "2z.mm"
include "efexp.mm"
include "sylancl.mm"
include "ccos.mm"
include "cre.mm"
include "recoscld.mm"
include "syl6eleq.mm"
include "sylib.mm"
include "simpld.mm"
include "sqrtcld.mm"
include "recld.mm"
include "cosq14ge0.mm"
include "sqrtrege0d.mm"
include "sincossq.mm"
include "sqsqrtd.mm"
include "2nn0.mm"
include "absexp.mm"
include "simprd.mm"
include "absvalsq2d.mm"
include "3eqtr2d.mm"
include "fveq1i.mm"
include "fvres.mm"
include "syl5eq.mm"
include "f1ocnvfv2.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "sincld.mm"
include "sqcld.mm"
include "coscld.mm"
include "pncan2d.mm"
include "pncand.mm"
include "sq11d.mm"
include "oveq2d.mm"
include "efival.mm"
include "replimd.mm"
include "3eqtr4d.mm"
include "mulid2d.mm"
include "eqeq12d.mm"
include "syl5ib.mm"
include "bitr2d.mm"
include "adantl.mm"
include "eqeq2d.mm"
include "3imtr4d.mm"
include "reximdva.mm"
include "mpd.mm"
include "dffo3.mm"
include "df-f1o.mm"

theorem efif1olem4
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  let cD: class D
  let cS: class S
  let cF: class F
  let cA: class A
  assume efif1o.1: |- F = ( w e. D |-> ( exp ` ( _i x. w ) ) )
  assume efif1o.2: |- C = ( `' abs " { 1 } )
  assume efif1olem4.3: |- ( ph -> D C_ RR )
  assume efif1olem4.4: |- ( ( ph /\ ( x e. D /\ y e. D ) ) -> ( abs ` ( x - y ) ) < ( 2 x. _pi ) )
  assume efif1olem4.5: |- ( ( ph /\ z e. RR ) -> E. y e. D ( ( z - y ) / ( 2 x. _pi ) ) e. ZZ )
  assume efif1olem4.6: |- S = ( sin |` ( -u ( _pi / 2 ) [,] ( _pi / 2 ) ) )

  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint F x
  disjoint F y
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint S y
  disjoint S z
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  assert |- ( ph -> F : D -1-1-onto-> C )

  proof
    wph
    cD
    cC
    cF
    wf1
    #
    cD
    cC
    cF
    wfo
    #
    cD
    cC
    cF
    wf1o
    wph
    cD
    cC
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    wceq
    #
    vx
    vy
    weq
    #
    wi
    #
    vy
    cD
    wral
    vx
    cD
    wral
    @0
    wph
    vw
    cD
    ci
    vw
    cv
    #
    cmul
    co
    #
    ce
    cfv
    #
    cC
    cF
    wph
    @10
    cD
    wcel
    wa
    @10
    cr
    wcel
    #
    @12
    cC
    wcel
    wph
    cD
    cr
    @10
    efif1olem4.3
    sselda
    @13
    @12
    cabs
    ccnv
    c1
    csn
    cima
    #
    cC
    @13
    @12
    cc
    wcel
    #
    @12
    cabs
    cfv
    c1
    wceq
    #
    @12
    @14
    wcel
    #
    @13
    @11
    cc
    wcel
    #
    @15
    @13
    ci
    cc
    wcel
    #
    @10
    cc
    wcel
    @18
    ax-icn
    @10
    recn
    ci
    @10
    mulcl
    sylancr
    @11
    efcl
    syl
    @10
    absefi
    cabs
    cc
    wfn
    #
    @17
    @15
    @16
    wa
    wb
    cc
    cr
    cabs
    wf
    @20
    absf
    cc
    cr
    cabs
    ffn
    ax-mp
    #
    cc
    c1
    @12
    cabs
    fniniseg
    ax-mp
    sylanbrc
    efif1o.2
    syl6eleqr
    syl
    efif1o.1
    fmptd
    #
    wph
    @9
    vx
    vy
    cD
    cD
    wph
    @3
    cD
    wcel
    #
    @5
    cD
    wcel
    #
    wa
    #
    wa
    #
    @7
    @8
    @26
    @7
    wa
    #
    @3
    @5
    @27
    @3
    @27
    cD
    cr
    @3
    wph
    cD
    cr
    wss
    #
    @25
    @7
    efif1olem4.3
    ad2antrr
    #
    wph
    @23
    @24
    @7
    simplrl
    #
    sseldd
    recnd
    #
    @27
    @5
    @27
    cD
    cr
    @5
    @29
    wph
    @23
    @24
    @7
    simplrr
    #
    sseldd
    recnd
    #
    @27
    @3
    @5
    cmin
    co
    #
    c2
    cpi
    cmul
    co
    #
    cdiv
    co
    #
    cc0
    wceq
    #
    @34
    cc0
    wceq
    #
    @27
    @36
    @27
    @34
    cc
    wcel
    #
    @36
    cc
    wcel
    #
    @27
    @3
    @5
    @31
    @33
    subcld
    #
    @39
    @35
    cc
    wcel
    #
    @35
    cc0
    wne
    #
    @40
    @35
    c2
    cpi
    2re
    pire
    remulcli
    #
    recni
    #
    @35
    @44
    c2
    cpi
    2re
    pire
    2pos
    pipos
    mulgt0ii
    #
    gt0ne0ii
    #
    @34
    @35
    divcl
    mp3an23
    syl
    @27
    @36
    cabs
    cfv
    #
    c1
    clt
    wbr
    #
    @48
    cc0
    wceq
    #
    @27
    @48
    @34
    cabs
    cfv
    #
    @35
    cdiv
    co
    #
    c1
    clt
    @27
    @48
    @51
    @35
    cabs
    cfv
    #
    cdiv
    co
    #
    @52
    @27
    @39
    @48
    @54
    wceq
    #
    @41
    @39
    @42
    @43
    @55
    @45
    @47
    @34
    @35
    absdiv
    mp3an23
    syl
    @53
    @35
    @51
    cdiv
    @35
    cr
    wcel
    #
    cc0
    @35
    cle
    wbr
    @53
    @35
    wceq
    @44
    cc0
    @35
    0re
    @44
    @46
    ltleii
    @35
    absid
    mp2an
    oveq2i
    syl6eq
    @27
    @52
    c1
    clt
    wbr
    #
    @51
    @35
    c1
    cmul
    co
    #
    clt
    wbr
    #
    @27
    @51
    @35
    @58
    clt
    @26
    @51
    @35
    clt
    wbr
    @7
    efif1olem4.4
    adantr
    @35
    @45
    mulid1i
    syl6breqr
    @27
    @51
    cr
    wcel
    #
    @57
    @59
    wb
    #
    @27
    @34
    @41
    abscld
    @60
    c1
    cr
    wcel
    @56
    cc0
    @35
    clt
    wbr
    #
    wa
    @61
    1re
    @56
    @62
    @44
    @46
    pm3.2i
    @51
    c1
    @35
    ltdivmul
    mp3an23
    syl
    mpbird
    eqbrtrd
    @27
    @48
    cn0
    wcel
    #
    @49
    @50
    wb
    @27
    @36
    cz
    wcel
    @63
    @27
    ci
    @34
    cmul
    co
    #
    ci
    @35
    cmul
    co
    #
    cdiv
    co
    #
    @36
    cz
    @27
    @39
    @66
    @36
    wceq
    #
    @41
    @39
    @42
    @43
    wa
    #
    @19
    ci
    cc0
    wne
    #
    wa
    #
    @67
    @42
    @43
    @45
    @47
    pm3.2i
    #
    @19
    @69
    ax-icn
    ine0
    pm3.2i
    #
    @34
    @35
    ci
    divcan5
    mp3an23
    syl
    @27
    @64
    ce
    cfv
    #
    c1
    wceq
    #
    @66
    cz
    wcel
    #
    @27
    @73
    ci
    @3
    cmul
    co
    #
    ci
    @5
    cmul
    co
    #
    cmin
    co
    #
    ce
    cfv
    #
    @76
    ce
    cfv
    #
    @77
    ce
    cfv
    #
    cdiv
    co
    #
    c1
    @27
    @64
    @78
    ce
    @27
    ci
    @3
    @5
    @19
    @27
    ax-icn
    a1i
    @31
    @33
    subdid
    fveq2d
    @27
    @76
    cc
    wcel
    #
    @77
    cc
    wcel
    #
    @79
    @82
    wceq
    @27
    @19
    @3
    cc
    wcel
    #
    @83
    ax-icn
    @31
    ci
    @3
    mulcl
    sylancr
    @27
    @19
    @5
    cc
    wcel
    #
    @84
    ax-icn
    @33
    ci
    @5
    mulcl
    #
    sylancr
    #
    @76
    @77
    efsub
    syl2anc
    @27
    @80
    @81
    @27
    @84
    @81
    cc
    wcel
    #
    @88
    @77
    efcl
    #
    syl
    @27
    @84
    @81
    cc0
    wne
    @88
    @77
    efne0
    syl
    @27
    @4
    @6
    @80
    @81
    @26
    @7
    simpr
    @27
    @23
    @4
    @80
    wceq
    @30
    vw
    @3
    @12
    @80
    cD
    cF
    vw
    vx
    weq
    @11
    @76
    ce
    @10
    @3
    ci
    cmul
    oveq2
    fveq2d
    efif1o.1
    @76
    ce
    fvex
    fvmpt
    syl
    @27
    @24
    @6
    @81
    wceq
    #
    @32
    vw
    @5
    @12
    @81
    cD
    cF
    vw
    vy
    weq
    @11
    @77
    ce
    @10
    @5
    ci
    cmul
    oveq2
    fveq2d
    efif1o.1
    @77
    ce
    fvex
    fvmpt
    #
    syl
    3eqtr3d
    diveq1bd
    3eqtrd
    @27
    @64
    cc
    wcel
    #
    @74
    @75
    wb
    @27
    @19
    @39
    @93
    ax-icn
    @41
    ci
    @34
    mulcl
    sylancr
    @64
    efeq1
    syl
    mpbid
    eqeltrrd
    @36
    nn0abscl
    syl
    @48
    nn0lt10b
    syl
    mpbid
    abs00d
    @27
    @39
    @37
    @38
    wb
    #
    @41
    @39
    @42
    @43
    @94
    @45
    @47
    @34
    @35
    diveq0
    mp3an23
    syl
    mpbid
    subeq0d
    ex
    ralrimivva
    vx
    vy
    cD
    cC
    cF
    dff13
    sylanbrc
    wph
    @2
    @3
    @6
    wceq
    #
    vy
    cD
    wrex
    #
    vx
    cC
    wral
    @1
    @22
    wph
    @96
    vx
    cC
    wph
    @3
    cC
    wcel
    #
    wa
    #
    c2
    @3
    csqrt
    cfv
    #
    cim
    cfv
    #
    cS
    ccnv
    #
    cfv
    #
    cmul
    co
    #
    @5
    cmin
    co
    #
    @35
    cdiv
    co
    #
    cz
    wcel
    #
    vy
    cD
    wrex
    #
    @96
    @98
    @103
    cr
    wcel
    #
    vz
    cv
    #
    @5
    cmin
    co
    #
    @35
    cdiv
    co
    #
    cz
    wcel
    #
    vy
    cD
    wrex
    #
    vz
    cr
    wral
    #
    @107
    @98
    c2
    cr
    wcel
    @102
    cr
    wcel
    @108
    2re
    @98
    cpi
    c2
    cdiv
    co
    #
    cneg
    #
    @115
    cicc
    co
    #
    cr
    @102
    @116
    cr
    wcel
    @115
    cr
    wcel
    @117
    cr
    wss
    neghalfpire
    halfpire
    @116
    @115
    iccssre
    mp2an
    @98
    @100
    c1
    cneg
    c1
    cicc
    co
    #
    wcel
    #
    @102
    @117
    wcel
    #
    wph
    vx
    vw
    cC
    cD
    cF
    efif1o.1
    efif1o.2
    efif1olem3
    #
    @118
    @117
    @100
    @101
    @117
    @118
    cS
    wf1o
    #
    @118
    @117
    @101
    wf1o
    @118
    @117
    @101
    wf
    @122
    @117
    @118
    csin
    @117
    cres
    #
    wf1o
    #
    resinf1o
    cS
    @123
    wceq
    @122
    @124
    wb
    efif1olem4.6
    @117
    @118
    cS
    @123
    f1oeq1
    ax-mp
    mpbir
    #
    @117
    @118
    cS
    f1ocnv
    @118
    @117
    @101
    f1of
    mp2b
    ffvelrni
    syl
    #
    sseldi
    #
    c2
    @102
    remulcl
    sylancr
    #
    wph
    @114
    @97
    wph
    @113
    vz
    cr
    efif1olem4.5
    ralrimiva
    adantr
    @113
    @107
    vz
    @103
    cr
    @109
    @103
    wceq
    #
    @112
    @106
    vy
    cD
    @129
    @111
    @105
    cz
    @129
    @110
    @104
    @35
    cdiv
    @109
    @103
    @5
    cmin
    oveq1
    oveq1d
    eleq1d
    rexbidv
    rspcv
    sylc
    @98
    @106
    @95
    vy
    cD
    @98
    @24
    wa
    #
    ci
    @104
    cmul
    co
    #
    ce
    cfv
    #
    c1
    wceq
    #
    @3
    @81
    wceq
    #
    @106
    @95
    @133
    @132
    @81
    cmul
    co
    #
    c1
    @81
    cmul
    co
    #
    wceq
    @130
    @134
    @132
    c1
    @81
    cmul
    oveq1
    @130
    @135
    @3
    @136
    @81
    @130
    @131
    @77
    caddc
    co
    #
    ce
    cfv
    #
    ci
    @103
    cmul
    co
    #
    ce
    cfv
    #
    @135
    @3
    @130
    @137
    @139
    ce
    @130
    @137
    @139
    @77
    cmin
    co
    #
    @77
    caddc
    co
    @139
    @130
    @131
    @141
    @77
    caddc
    @130
    ci
    @103
    @5
    @19
    @130
    ax-icn
    a1i
    @130
    @103
    @98
    @108
    @24
    @128
    adantr
    recnd
    #
    @130
    @5
    @130
    cD
    cr
    @5
    wph
    @28
    @97
    @24
    efif1olem4.3
    ad2antrr
    @98
    @24
    simpr
    sseldd
    recnd
    #
    subdid
    oveq1d
    @130
    @139
    @77
    @130
    @19
    @103
    cc
    wcel
    @139
    cc
    wcel
    ax-icn
    @142
    ci
    @103
    mulcl
    sylancr
    @130
    @19
    @86
    @84
    ax-icn
    @143
    @87
    sylancr
    #
    npcand
    eqtrd
    fveq2d
    @130
    @131
    cc
    wcel
    #
    @84
    @138
    @135
    wceq
    @130
    @19
    @104
    cc
    wcel
    #
    @145
    ax-icn
    @130
    @103
    @5
    @142
    @143
    subcld
    #
    ci
    @104
    mulcl
    sylancr
    #
    @144
    @131
    @77
    efadd
    syl2anc
    @98
    @140
    @3
    wceq
    @24
    @98
    @140
    ci
    @102
    cmul
    co
    #
    ce
    cfv
    #
    c2
    cexp
    co
    #
    @99
    c2
    cexp
    co
    #
    @3
    @98
    @140
    c2
    @149
    cmul
    co
    #
    ce
    cfv
    #
    @151
    @98
    @139
    @153
    ce
    @98
    @102
    cc
    wcel
    #
    @139
    @153
    wceq
    #
    @98
    @102
    @127
    recnd
    #
    @19
    c2
    cc
    wcel
    @155
    @156
    ax-icn
    2cn
    ci
    c2
    @102
    mul12
    mp3an12
    syl
    fveq2d
    @98
    @149
    cc
    wcel
    #
    c2
    cz
    wcel
    @154
    @151
    wceq
    @98
    @19
    @155
    @158
    ax-icn
    @157
    ci
    @102
    mulcl
    sylancr
    2z
    @149
    c2
    efexp
    sylancl
    eqtrd
    @98
    @150
    @99
    c2
    cexp
    @98
    @102
    ccos
    cfv
    #
    ci
    @102
    csin
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    @99
    cre
    cfv
    #
    ci
    @100
    cmul
    co
    #
    caddc
    co
    @150
    @99
    @98
    @159
    @163
    @161
    @164
    caddc
    @98
    @159
    @163
    @98
    @102
    @127
    recoscld
    @98
    @99
    @98
    @3
    @98
    @85
    @3
    cabs
    cfv
    #
    c1
    wceq
    #
    @98
    @3
    @14
    wcel
    #
    @85
    @166
    wa
    #
    @98
    @3
    cC
    @14
    wph
    @97
    simpr
    efif1o.2
    syl6eleq
    @20
    @167
    @168
    wb
    @21
    cc
    c1
    @3
    cabs
    fniniseg
    ax-mp
    sylib
    #
    simpld
    #
    sqrtcld
    #
    recld
    #
    @98
    @120
    cc0
    @159
    cle
    wbr
    @126
    @102
    cosq14ge0
    syl
    @98
    @3
    @170
    sqrtrege0d
    @98
    @160
    c2
    cexp
    co
    #
    @159
    c2
    cexp
    co
    #
    caddc
    co
    #
    @173
    cmin
    co
    @163
    c2
    cexp
    co
    #
    @100
    c2
    cexp
    co
    #
    caddc
    co
    #
    @177
    cmin
    co
    @174
    @176
    @98
    @175
    @178
    @173
    @177
    cmin
    @98
    @175
    c1
    @99
    cabs
    cfv
    c2
    cexp
    co
    #
    @178
    @98
    @155
    @175
    c1
    wceq
    @157
    @102
    sincossq
    syl
    @98
    @152
    cabs
    cfv
    #
    @165
    @179
    c1
    @98
    @152
    @3
    cabs
    @98
    @3
    @170
    sqsqrtd
    #
    fveq2d
    @98
    @99
    cc
    wcel
    c2
    cn0
    wcel
    @180
    @179
    wceq
    @171
    2nn0
    @99
    c2
    absexp
    sylancl
    @98
    @85
    @166
    @169
    simprd
    3eqtr3d
    @98
    @99
    @171
    absvalsq2d
    3eqtr2d
    @98
    @160
    @100
    c2
    cexp
    @98
    @102
    cS
    cfv
    #
    @160
    @100
    @98
    @182
    @102
    @123
    cfv
    #
    @160
    @102
    cS
    @123
    efif1olem4.6
    fveq1i
    @98
    @120
    @183
    @160
    wceq
    @126
    @102
    @117
    csin
    fvres
    syl
    syl5eq
    @98
    @122
    @119
    @182
    @100
    wceq
    @125
    @121
    @117
    @118
    @100
    cS
    f1ocnvfv2
    sylancr
    eqtr3d
    #
    oveq1d
    #
    oveq12d
    @98
    @173
    @174
    @98
    @160
    @98
    @102
    @157
    sincld
    sqcld
    #
    @98
    @159
    @98
    @102
    @157
    coscld
    sqcld
    pncan2d
    @98
    @176
    @177
    @98
    @163
    @98
    @163
    @172
    recnd
    sqcld
    @98
    @173
    @177
    cc
    @185
    @186
    eqeltrrd
    pncand
    3eqtr3d
    sq11d
    @98
    @160
    @100
    ci
    cmul
    @184
    oveq2d
    oveq12d
    @98
    @155
    @150
    @162
    wceq
    @157
    @102
    efival
    syl
    @98
    @99
    @171
    replimd
    3eqtr4d
    oveq1d
    @181
    3eqtrd
    adantr
    3eqtr3d
    @130
    @81
    @130
    @84
    @89
    @144
    @90
    syl
    mulid2d
    eqeq12d
    syl5ib
    @130
    @133
    @131
    @65
    cdiv
    co
    #
    cz
    wcel
    #
    @106
    @130
    @145
    @133
    @188
    wb
    @148
    @131
    efeq1
    syl
    @130
    @187
    @105
    cz
    @130
    @146
    @187
    @105
    wceq
    #
    @147
    @146
    @68
    @70
    @189
    @71
    @72
    @104
    @35
    ci
    divcan5
    mp3an23
    syl
    eleq1d
    bitr2d
    @130
    @6
    @81
    @3
    @24
    @91
    @98
    @92
    adantl
    eqeq2d
    3imtr4d
    reximdva
    mpd
    ralrimiva
    vy
    vx
    cD
    cC
    cF
    dffo3
    sylanbrc
    cD
    cC
    cF
    df-f1o
    sylanbrc
end
