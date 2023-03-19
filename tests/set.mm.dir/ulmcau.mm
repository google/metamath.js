include "culm.mm"
include "cfv.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "cuz.mm"
include "wrex.mm"
include "crp.mm"
include "wex.mm"
include "eldmg.mm"
include "ibi.mm"
include "wa.mm"
include "c2.mm"
include "cdiv.mm"
include "cz.mm"
include "ad2antrr.mm"
include "cc.mm"
include "cmap.mm"
include "wf.mm"
include "eqidd.mm"
include "simplr.mm"
include "rphalfcl.mm"
include "adantl.mm"
include "ulmi.mm"
include "wi.mm"
include "simpr.mm"
include "syl6eleq.mm"
include "eluzelz.mm"
include "uzid.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "ralbidv.mm"
include "rspcv.mm"
include "4syl.mm"
include "r19.26.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "elmapi.mm"
include "syl.mm"
include "ulmcl.mm"
include "ad4antlr.mm"
include "abssubd.mm"
include "biimpd.mm"
include "cr.mm"
include "uztrn2.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "anassrs.mm"
include "rpre.mm"
include "abs3lem.mm"
include "syl22anc.mm"
include "sylan2d.mm"
include "ancomsd.mm"
include "ralimdva.mm"
include "syl5bir.mm"
include "expdimp.mm"
include "an32s.mm"
include "ex.mm"
include "com23.mm"
include "mpdd.mm"
include "reximdva.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "exlimdv.mm"
include "syl5.mm"
include "wrel.mm"
include "cmpt.mm"
include "cli.mm"
include "ulmrel.mm"
include "ulmcaulem.mm"
include "biimpa.mm"
include "wceq.mm"
include "breq2.mm"
include "2ralbidv.mm"
include "rexbidv.mm"
include "ralcom.mm"
include "oveq12d.mm"
include "cbvralv.mm"
include "syl5bb.mm"
include "raleqbidv.mm"
include "raleqdv.mm"
include "cbvrexv.mm"
include "syl6bbr.mm"
include "rspccva.mm"
include "eqid.mm"
include "eleq2s.mm"
include "ad2antlr.mm"
include "sylan.mm"
include "fvex.mm"
include "fvmpt.mm"
include "cvv.mm"
include "fmptd.mm"
include "ralimdv.mm"
include "reximdv.mm"
include "impcom.mm"
include "adantll.mm"
include "oveq2d.mm"
include "ralbidva.mm"
include "rexbiia.mm"
include "bitri.mm"
include "sylibr.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "caucvg.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "climdm.mm"
include "sylib.mm"
include "climi2.mm"
include "r19.29uz.mm"
include "r19.2uz.mm"
include "climcl.mm"
include "ad5antr.mm"
include "ffvelrnd.mm"
include "rexlimdva.mm"
include "mpan2d.mm"
include "sylan2.mm"
include "ulm2.mm"
include "mpbird.mm"
include "releldm.mm"
include "sylancr.mm"
include "impbid.mm"

theorem ulmcau
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  assume ulmcau.z: |- Z = ( ZZ>= ` M )
  assume ulmcau.m: |- ( ph -> M e. ZZ )
  assume ulmcau.s: |- ( ph -> S e. V )
  assume ulmcau.f: |- ( ph -> F : Z --> ( CC ^m S ) )

  disjoint j k
  disjoint j x
  disjoint j z
  disjoint F j
  disjoint k x
  disjoint k z
  disjoint F k
  disjoint x z
  disjoint F x
  disjoint F z
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint ph z
  disjoint S j
  disjoint S k
  disjoint S x
  disjoint S z
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint Z z
  disjoint M j
  disjoint M k
  disjoint M z
  disjoint g j
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g p
  disjoint g q
  disjoint g r
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint j m
  disjoint j n
  disjoint j p
  disjoint j q
  disjoint j r
  disjoint j v
  disjoint j w
  disjoint j y
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k q
  disjoint k r
  disjoint k v
  disjoint k w
  disjoint k y
  disjoint m n
  disjoint m p
  disjoint m q
  disjoint m r
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n p
  disjoint n q
  disjoint n r
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint p q
  disjoint p r
  disjoint p v
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q r
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint F q
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint F r
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint y z
  disjoint F y
  disjoint g ph
  disjoint m ph
  disjoint n ph
  disjoint p ph
  disjoint ph q
  disjoint ph r
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint S g
  disjoint S m
  disjoint S n
  disjoint S p
  disjoint S q
  disjoint S r
  disjoint S v
  disjoint S w
  disjoint S y
  disjoint Z g
  disjoint Z m
  disjoint Z n
  disjoint Z p
  disjoint Z q
  disjoint Z r
  disjoint Z v
  disjoint Z w
  disjoint Z y
  disjoint M p
  disjoint M q
  disjoint M r
  disjoint M w
  assert |- ( ph -> ( F e. dom ( ~~>u ` S ) <-> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) A. z e. S ( abs ` ( ( ( F ` k ) ` z ) - ( ( F ` j ) ` z ) ) ) < x ) )

  proof
    wph
    cF
    cS
    culm
    cfv
    #
    cdm
    #
    wcel
    #
    vz
    cv
    #
    vk
    cv
    #
    cF
    cfv
    #
    cfv
    #
    @3
    vj
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    @7
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @2
    cF
    vg
    cv
    #
    @0
    wbr
    #
    vg
    wex
    #
    wph
    @18
    @2
    @21
    vg
    cF
    @0
    @1
    eldmg
    ibi
    wph
    @20
    @18
    vg
    wph
    @20
    @18
    wph
    @20
    wa
    #
    @17
    vx
    crp
    @22
    @12
    crp
    wcel
    #
    wa
    #
    @6
    @3
    @19
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @12
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    @15
    wral
    #
    vj
    cZ
    wrex
    @17
    @24
    vz
    @25
    @6
    @28
    cS
    vj
    vk
    cF
    @19
    cM
    cZ
    ulmcau.z
    wph
    cM
    cz
    wcel
    #
    @20
    @23
    ulmcau.m
    ad2antrr
    wph
    cZ
    cc
    cS
    cmap
    co
    #
    cF
    wf
    #
    @20
    @23
    ulmcau.f
    ad2antrr
    #
    @24
    @4
    cZ
    wcel
    #
    @3
    cS
    wcel
    #
    wa
    wa
    @6
    eqidd
    @24
    @37
    wa
    @25
    eqidd
    wph
    @20
    @23
    simplr
    @23
    @28
    crp
    wcel
    @22
    @12
    rphalfcl
    adantl
    ulmi
    @24
    @31
    @16
    vj
    cZ
    @24
    @7
    cZ
    wcel
    #
    wa
    #
    @31
    @9
    @25
    cmin
    co
    #
    cabs
    cfv
    #
    @28
    clt
    wbr
    #
    vz
    cS
    wral
    #
    @16
    @39
    @7
    cM
    cuz
    cfv
    #
    wcel
    @7
    cz
    wcel
    @7
    @15
    wcel
    @31
    @43
    wi
    @39
    @7
    cZ
    @44
    @24
    @38
    simpr
    ulmcau.z
    syl6eleq
    cM
    @7
    eluzelz
    @7
    uzid
    @30
    @43
    vk
    @7
    @15
    vk
    vj
    weq
    #
    @29
    @42
    vz
    cS
    @45
    @27
    @41
    @28
    clt
    @45
    @26
    @40
    cabs
    @45
    @6
    @9
    @25
    cmin
    @45
    @3
    @5
    @8
    @4
    @7
    cF
    fveq2
    fveq1d
    oveq1d
    fveq2d
    breq1d
    ralbidv
    rspcv
    4syl
    @39
    @43
    @31
    @16
    @39
    @43
    @31
    @16
    wi
    @39
    @43
    wa
    @30
    @14
    vk
    @15
    @39
    @4
    @15
    wcel
    #
    @43
    @30
    @14
    wi
    @39
    @46
    wa
    #
    @43
    @30
    @14
    @43
    @30
    wa
    @42
    @29
    wa
    #
    vz
    cS
    wral
    @47
    @14
    @42
    @29
    vz
    cS
    r19.26
    @47
    @48
    @13
    vz
    cS
    @47
    @37
    wa
    #
    @29
    @42
    @13
    @49
    @42
    @25
    @9
    cmin
    co
    cabs
    cfv
    #
    @28
    clt
    wbr
    #
    @29
    @13
    @49
    @42
    @51
    @49
    @41
    @50
    @28
    clt
    @49
    @9
    @25
    @47
    cS
    cc
    @3
    @8
    @47
    @8
    @33
    wcel
    #
    cS
    cc
    @8
    wf
    @39
    @52
    @46
    @24
    cZ
    @33
    @7
    cF
    @35
    ffvelrnda
    adantr
    @8
    cc
    cS
    elmapi
    syl
    ffvelrnda
    #
    @47
    cS
    cc
    @3
    @19
    @20
    cS
    cc
    @19
    wf
    wph
    @23
    @38
    @46
    cS
    cF
    @19
    ulmcl
    ad4antlr
    ffvelrnda
    #
    abssubd
    breq1d
    biimpd
    @49
    @6
    cc
    wcel
    @9
    cc
    wcel
    @25
    cc
    wcel
    @12
    cr
    wcel
    #
    @29
    @51
    wa
    @13
    wi
    @47
    cS
    cc
    @3
    @5
    @47
    @5
    @33
    wcel
    #
    cS
    cc
    @5
    wf
    @24
    @38
    @46
    @56
    @24
    @34
    @36
    @56
    @38
    @46
    wa
    #
    @35
    cM
    @4
    @7
    cZ
    ulmcau.z
    uztrn2
    #
    cZ
    @33
    @4
    cF
    ffvelrn
    syl2an
    anassrs
    @5
    cc
    cS
    elmapi
    syl
    ffvelrnda
    @53
    @54
    @23
    @55
    @22
    @38
    @46
    @37
    @12
    rpre
    ad4antlr
    @6
    @9
    @25
    @12
    abs3lem
    syl22anc
    sylan2d
    ancomsd
    ralimdva
    syl5bir
    expdimp
    an32s
    ralimdva
    ex
    com23
    mpdd
    reximdva
    mpd
    ralrimiva
    ex
    exlimdv
    syl5
    wph
    @18
    @2
    wph
    @18
    wa
    #
    @0
    wrel
    cF
    vy
    cS
    vn
    cZ
    vy
    cv
    #
    vn
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmpt
    #
    cli
    cfv
    #
    cmpt
    #
    @0
    wbr
    #
    @2
    cS
    ulmrel
    @59
    @67
    vw
    cv
    #
    vq
    cv
    #
    cF
    cfv
    #
    cfv
    #
    vn
    cZ
    @68
    @62
    cfv
    #
    cmpt
    #
    cli
    cfv
    #
    cmin
    co
    cabs
    cfv
    vr
    cv
    #
    clt
    wbr
    #
    vw
    cS
    wral
    #
    vq
    vp
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vp
    cZ
    wrex
    #
    vr
    crp
    wral
    @59
    @81
    vr
    crp
    @59
    @75
    crp
    wcel
    #
    wa
    #
    @71
    @68
    vm
    cv
    #
    cF
    cfv
    #
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @75
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    vm
    @69
    cuz
    cfv
    #
    wral
    #
    vw
    cS
    wral
    #
    vq
    @79
    wral
    #
    vp
    cZ
    wrex
    #
    @81
    @59
    @6
    @3
    @85
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @12
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vm
    @4
    cuz
    cfv
    #
    wral
    vk
    @15
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @89
    crp
    wcel
    #
    @95
    @82
    wph
    @18
    @104
    wph
    vx
    vz
    cS
    vj
    vk
    vm
    cF
    cM
    cV
    cZ
    ulmcau.z
    ulmcau.m
    ulmcau.s
    ulmcau.f
    ulmcaulem
    biimpa
    @75
    rphalfcl
    #
    @103
    @95
    vx
    @89
    crp
    @12
    @89
    wceq
    #
    @103
    @98
    @89
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vm
    @101
    wral
    #
    vk
    @15
    wral
    #
    vj
    cZ
    wrex
    @95
    @107
    @102
    @111
    vj
    cZ
    @107
    @100
    @109
    vk
    vm
    @15
    @101
    @107
    @99
    @108
    vz
    cS
    @12
    @89
    @98
    clt
    breq2
    ralbidv
    2ralbidv
    rexbidv
    @94
    @111
    vp
    vj
    cZ
    @94
    @110
    vk
    @79
    wral
    vp
    vj
    weq
    #
    @111
    @93
    @110
    vq
    vk
    @79
    @93
    @90
    vw
    cS
    wral
    #
    vm
    @91
    wral
    vq
    vk
    weq
    #
    @110
    @90
    vw
    vm
    cS
    @91
    ralcom
    @114
    @113
    @109
    vm
    @91
    @101
    @69
    @4
    cuz
    fveq2
    @113
    @3
    @70
    cfv
    #
    @96
    cmin
    co
    #
    cabs
    cfv
    #
    @89
    clt
    wbr
    #
    vz
    cS
    wral
    @114
    @109
    @90
    @118
    vw
    vz
    cS
    vw
    vz
    weq
    #
    @88
    @117
    @89
    clt
    @119
    @87
    @116
    cabs
    @119
    @71
    @115
    @86
    @96
    cmin
    @68
    @3
    @70
    fveq2
    @68
    @3
    @85
    fveq2
    oveq12d
    fveq2d
    breq1d
    cbvralv
    @114
    @118
    @108
    vz
    cS
    @114
    @117
    @98
    @89
    clt
    @114
    @116
    @97
    cabs
    @114
    @115
    @6
    @96
    cmin
    @114
    @3
    @70
    @5
    @69
    @4
    cF
    fveq2
    fveq1d
    oveq1d
    fveq2d
    breq1d
    ralbidv
    syl5bb
    raleqbidv
    syl5bb
    cbvralv
    @112
    @110
    vk
    @79
    @15
    @78
    @7
    cuz
    fveq2
    #
    raleqdv
    syl5bb
    cbvrexv
    syl6bbr
    rspccva
    syl2an
    @83
    @94
    @80
    vp
    cZ
    @83
    @78
    cZ
    wcel
    #
    wa
    @93
    @77
    vq
    @79
    @83
    @121
    @69
    @79
    wcel
    #
    @93
    @77
    wi
    #
    @121
    @122
    wa
    @83
    @69
    cZ
    wcel
    #
    @123
    cM
    @69
    @78
    cZ
    ulmcau.z
    uztrn2
    @83
    @124
    wa
    #
    @92
    @76
    vw
    cS
    @125
    @68
    cS
    wcel
    #
    wa
    #
    @92
    @86
    @74
    cmin
    co
    cabs
    cfv
    @89
    clt
    wbr
    #
    vm
    vv
    cv
    cuz
    cfv
    #
    wral
    vv
    @91
    wrex
    #
    @76
    @127
    @74
    @86
    @89
    vv
    vm
    @73
    @69
    @91
    @91
    eqid
    #
    @124
    @69
    cz
    wcel
    #
    @83
    @126
    @132
    @69
    @44
    cZ
    cM
    @69
    eluzelz
    ulmcau.z
    eleq2s
    ad2antlr
    @83
    @105
    @124
    @126
    @82
    @105
    @59
    @106
    adantl
    ad2antrr
    @127
    @84
    @91
    wcel
    #
    wa
    #
    @84
    cZ
    wcel
    #
    @84
    @73
    cfv
    @86
    wceq
    @127
    @124
    @133
    @135
    @83
    @124
    @126
    simplr
    cM
    @84
    @69
    cZ
    ulmcau.z
    uztrn2
    sylan
    #
    vn
    @84
    @72
    @86
    cZ
    @73
    vn
    vm
    weq
    @68
    @62
    @85
    @61
    @84
    cF
    fveq2
    fveq1d
    @73
    eqid
    @68
    @85
    fvex
    fvmpt
    syl
    @127
    @73
    cli
    cdm
    #
    wcel
    #
    @73
    @74
    cli
    wbr
    #
    @125
    @64
    @137
    wcel
    #
    vy
    cS
    wral
    #
    @126
    @138
    @59
    @141
    @82
    @124
    @59
    @140
    vy
    cS
    @59
    @60
    cS
    wcel
    #
    wa
    #
    vr
    vp
    vq
    @64
    cM
    cvv
    cZ
    ulmcau.z
    @143
    cZ
    cc
    @69
    @64
    @143
    vn
    cZ
    @63
    cc
    @64
    @59
    @61
    cZ
    wcel
    #
    @142
    @63
    cc
    wcel
    @59
    @144
    wa
    #
    cS
    cc
    @60
    @62
    @145
    @62
    @33
    wcel
    cS
    cc
    @62
    wf
    @59
    cZ
    @33
    @61
    cF
    wph
    @34
    @18
    ulmcau.f
    adantr
    #
    ffvelrnda
    @62
    cc
    cS
    elmapi
    syl
    ffvelrnda
    an32s
    @64
    eqid
    #
    fmptd
    ffvelrnda
    @143
    @60
    @5
    cfv
    #
    @60
    @8
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @12
    clt
    wbr
    #
    vk
    @15
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @69
    @64
    cfv
    #
    @78
    @64
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @75
    clt
    wbr
    #
    vq
    @79
    wral
    #
    vp
    cZ
    wrex
    #
    vr
    crp
    wral
    @18
    @142
    @155
    wph
    @142
    @18
    @155
    @142
    @17
    @154
    vx
    crp
    @142
    @16
    @153
    vj
    cZ
    @142
    @14
    @152
    vk
    @15
    @13
    @152
    vz
    @60
    cS
    vz
    vy
    weq
    #
    @11
    @151
    @12
    clt
    @163
    @10
    @150
    cabs
    @163
    @6
    @148
    @9
    @149
    cmin
    @3
    @60
    @5
    fveq2
    @3
    @60
    @8
    fveq2
    oveq12d
    fveq2d
    breq1d
    rspcv
    ralimdv
    reximdv
    ralimdv
    impcom
    adantll
    @162
    @154
    vr
    vx
    crp
    @162
    @151
    @75
    clt
    wbr
    #
    vk
    @15
    wral
    #
    vj
    cZ
    wrex
    #
    vr
    vx
    weq
    #
    @154
    @162
    @4
    @64
    cfv
    #
    @7
    @64
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @75
    clt
    wbr
    #
    vk
    @15
    wral
    #
    vj
    cZ
    wrex
    @166
    @161
    @173
    vp
    vj
    cZ
    @161
    @168
    @157
    cmin
    co
    #
    cabs
    cfv
    #
    @75
    clt
    wbr
    #
    vk
    @79
    wral
    @112
    @173
    @160
    @176
    vq
    vk
    @79
    @114
    @159
    @175
    @75
    clt
    @114
    @158
    @174
    cabs
    @114
    @156
    @168
    @157
    cmin
    @69
    @4
    @64
    fveq2
    oveq1d
    fveq2d
    breq1d
    cbvralv
    @112
    @176
    @172
    vk
    @79
    @15
    @120
    @112
    @175
    @171
    @75
    clt
    @112
    @174
    @170
    cabs
    @112
    @157
    @169
    @168
    cmin
    @78
    @7
    @64
    fveq2
    oveq2d
    fveq2d
    breq1d
    raleqbidv
    syl5bb
    cbvrexv
    @173
    @165
    vj
    cZ
    @38
    @172
    @164
    vk
    @15
    @57
    @171
    @151
    @75
    clt
    @57
    @170
    @150
    cabs
    @57
    @168
    @148
    @169
    @149
    cmin
    @57
    @36
    @168
    @148
    wceq
    @58
    vn
    @4
    @63
    @148
    cZ
    @64
    vn
    vk
    weq
    @60
    @62
    @5
    @61
    @4
    cF
    fveq2
    fveq1d
    @147
    @60
    @5
    fvex
    fvmpt
    syl
    @38
    @169
    @149
    wceq
    @46
    vn
    @7
    @63
    @149
    cZ
    @64
    vn
    vj
    weq
    @60
    @62
    @8
    @61
    @7
    cF
    fveq2
    fveq1d
    @147
    @60
    @8
    fvex
    fvmpt
    adantr
    oveq12d
    fveq2d
    breq1d
    ralbidva
    rexbiia
    bitri
    @167
    @165
    @153
    vj
    cZ
    @167
    @164
    @152
    vk
    @15
    @75
    @12
    @151
    clt
    breq2
    ralbidv
    rexbidv
    syl5bb
    cbvralv
    sylibr
    @64
    cvv
    wcel
    @143
    vn
    cZ
    @63
    cZ
    @44
    cvv
    ulmcau.z
    cM
    cuz
    fvex
    eqeltri
    mptex
    a1i
    caucvg
    #
    ralrimiva
    ad2antrr
    @140
    @138
    vy
    @68
    cS
    vy
    vw
    weq
    #
    @64
    @73
    @137
    @178
    vn
    cZ
    @63
    @72
    @60
    @68
    @62
    fveq2
    mpteq2dv
    #
    eleq1d
    rspccva
    sylan
    @73
    climdm
    sylib
    #
    climi2
    @92
    @130
    wa
    #
    @90
    @128
    wa
    #
    vm
    @91
    wrex
    #
    @127
    @76
    @181
    @182
    vm
    @129
    wral
    vv
    @91
    wrex
    @183
    @90
    @128
    vv
    vm
    @69
    @91
    @131
    r19.29uz
    @182
    vv
    vm
    @69
    @91
    @131
    r19.2uz
    syl
    @127
    @182
    @76
    vm
    @91
    @134
    @71
    cc
    wcel
    #
    @74
    cc
    wcel
    #
    @86
    cc
    wcel
    @75
    cr
    wcel
    #
    @182
    @76
    wi
    @127
    @184
    @133
    @125
    cS
    cc
    @68
    @70
    @125
    @70
    @33
    wcel
    cS
    cc
    @70
    wf
    @83
    cZ
    @33
    @69
    cF
    wph
    @34
    @18
    @82
    ulmcau.f
    ad2antrr
    ffvelrnda
    @70
    cc
    cS
    elmapi
    syl
    ffvelrnda
    adantr
    @127
    @185
    @133
    @127
    @139
    @185
    @180
    @74
    @73
    climcl
    syl
    adantr
    @134
    cS
    cc
    @68
    @85
    @134
    @85
    @33
    wcel
    cS
    cc
    @85
    wf
    @134
    cZ
    @33
    @84
    cF
    wph
    @34
    @18
    @82
    @124
    @126
    @133
    ulmcau.f
    ad5antr
    @136
    ffvelrnd
    @85
    cc
    cS
    elmapi
    syl
    @125
    @126
    @133
    simplr
    ffvelrnd
    @82
    @186
    @59
    @124
    @126
    @133
    @75
    rpre
    ad4antlr
    @71
    @74
    @86
    @75
    abs3lem
    syl22anc
    rexlimdva
    syl5
    mpan2d
    ralimdva
    sylan2
    anassrs
    ralimdva
    reximdva
    mpd
    ralrimiva
    @59
    vr
    vw
    @74
    @71
    cS
    vp
    vq
    cF
    @66
    cM
    cV
    cZ
    ulmcau.z
    wph
    @32
    @18
    ulmcau.m
    adantr
    @146
    @59
    @124
    @126
    wa
    wa
    @71
    eqidd
    @126
    @68
    @66
    cfv
    @74
    wceq
    @59
    vy
    @68
    @65
    @74
    cS
    @66
    @178
    @64
    @73
    cli
    @179
    fveq2d
    @66
    eqid
    #
    @73
    cli
    fvex
    fvmpt
    adantl
    @59
    vy
    cS
    @65
    cc
    @66
    @143
    @64
    @65
    cli
    wbr
    #
    @65
    cc
    wcel
    @143
    @140
    @188
    @177
    @64
    climdm
    sylib
    @65
    @64
    climcl
    syl
    @187
    fmptd
    wph
    cS
    cV
    wcel
    @18
    ulmcau.s
    adantr
    ulm2
    mpbird
    cF
    @66
    @0
    releldm
    sylancr
    ex
    impbid
end
