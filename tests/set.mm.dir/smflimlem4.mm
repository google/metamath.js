include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cin.mm"
include "wss.mm"
include "inss1.mm"
include "a1i.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "crp.mm"
include "wral.mm"
include "cr.mm"
include "sselda.mm"
include "cmpt.mm"
include "cli.mm"
include "cvv.mm"
include "wceq.mm"
include "nfv.mm"
include "nfcv.mm"
include "cdm.mm"
include "wf.mm"
include "csalg.mm"
include "adantr.mm"
include "csmblfn.mm"
include "ffvelrnda.mm"
include "eqid.mm"
include "smff.mm"
include "adantlr.mm"
include "cuz.mm"
include "ciin.mm"
include "ciun.mm"
include "crab.mm"
include "fveq2.mm"
include "mpteq2dv.mm"
include "eleq1d.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "simpr.mm"
include "fnlimfvre.mm"
include "elexd.mm"
include "fvmpt2d.mm"
include "eqeltrd.mm"
include "syldan.mm"
include "rpre.mm"
include "adantl.mm"
include "readdcld.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "w3a.mm"
include "wrex.mm"
include "c1.mm"
include "cn.mm"
include "rphalfcl.mm"
include "rpgtrecnn.mm"
include "syl.mm"
include "ad4antr.mm"
include "ad5ant15.mm"
include "ad3antrrr.mm"
include "cmpt2.mm"
include "breq1d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "breq2d.mm"
include "rabbidv.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "cbvmpt22.mm"
include "fveq2d.mm"
include "simpll.mm"
include "iineq2dv.mm"
include "iuneq2dv.mm"
include "cbviinv.mm"
include "crn.mm"
include "simp-4r.mm"
include "simplr.mm"
include "ad3antlr.mm"
include "smflimlem3.mm"
include "exp31.mm"
include "rexlimdv.mm"
include "mpd.mm"
include "cmin.mm"
include "cabs.mm"
include "cz.mm"
include "ad2antrr.mm"
include "wi.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "dmeqd.mm"
include "feq12d.mm"
include "imbi12d.mm"
include "chvarv.mm"
include "ad4ant14.mm"
include "iuneq2i.mm"
include "iineq1d.mm"
include "cbviunv.mm"
include "rabeqi.mm"
include "fveq1d.mm"
include "cbvmptv.mm"
include "eqcomi.mm"
include "eleq1i.mm"
include "rabbii.mm"
include "3eqtri.mm"
include "fveq2i.mm"
include "mpteq2i.mm"
include "fnlimabslt.mm"
include "resubcld.mm"
include "adantrr.mm"
include "recnd.mm"
include "abscld.mm"
include "rehalfcld.mm"
include "ad2antlr.mm"
include "leabsd.mm"
include "cc.mm"
include "recn.mm"
include "abssubd.mm"
include "simprr.mm"
include "eqbrtrd.mm"
include "lelttrd.mm"
include "simprl.mm"
include "ltsubadd2d.mm"
include "mpbid.mm"
include "ex.mm"
include "ralimdva.mm"
include "reximdai.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "oveq1d.mm"
include "rexanuz3.mm"
include "df-3an.mm"
include "3ancomb.mm"
include "bitr3i.mm"
include "rexbii.mm"
include "sylib.mm"
include "3adant3.mm"
include "simp3.mm"
include "ffvelrnd.mm"
include "ad4ant134.mm"
include "simpllr.mm"
include "adantlllr.mm"
include "3ad2antr1.mm"
include "rehalfcl.mm"
include "jca.mm"
include "readdcl.mm"
include "ad5ant13.mm"
include "simpr2.mm"
include "ltadd1dd.mm"
include "3adantr2.mm"
include "lttrd.mm"
include "addassd.mm"
include "2halves.mm"
include "breqtrd.mm"
include "ltled.mm"
include "ralrimiva.mm"
include "wb.mm"
include "alrple.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ssrabdv.mm"

theorem smflimlem4
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cD: class D
  let cP: class P
  let cS: class S
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cM: class M
  let cZ: class Z
  let vs: setvar s
  let vr: setvar r
  let vi: setvar i
  let vj: setvar j
  let vz: setvar z
  let vy: setvar y
  let vl: setvar l
  assume smflimlem4.1: |- ( ph -> M e. ZZ )
  assume smflimlem4.2: |- Z = ( ZZ>= ` M )
  assume smflimlem4.3: |- ( ph -> S e. SAlg )
  assume smflimlem4.4: |- ( ph -> F : Z --> ( SMblFn ` S ) )
  assume smflimlem4.5: |- D = { x e. U_ n e. Z |^|_ m e. ( ZZ>= ` n ) dom ( F ` m ) | ( m e. Z |-> ( ( F ` m ) ` x ) ) e. dom ~~> }
  assume smflimlem4.6: |- G = ( x e. D |-> ( ~~> ` ( m e. Z |-> ( ( F ` m ) ` x ) ) ) )
  assume smflimlem4.7: |- ( ph -> A e. RR )
  assume smflimlem4.8: |- P = ( m e. Z , k e. NN |-> { s e. S | { x e. dom ( F ` m ) | ( ( F ` m ) ` x ) < ( A + ( 1 / k ) ) } = ( s i^i dom ( F ` m ) ) } )
  assume smflimlem4.9: |- H = ( m e. Z , k e. NN |-> ( C ` ( m P k ) ) )
  assume smflimlem4.10: |- I = |^|_ k e. NN U_ n e. Z |^|_ m e. ( ZZ>= ` n ) ( m H k )
  assume smflimlem4.11: |- ( ( ph /\ r e. ran P ) -> ( C ` r ) e. r )

  disjoint A k
  disjoint A m
  disjoint A s
  disjoint k m
  disjoint k s
  disjoint m s
  disjoint A x
  disjoint k x
  disjoint m x
  disjoint C k
  disjoint C m
  disjoint C s
  disjoint C r
  disjoint k r
  disjoint D k
  disjoint D m
  disjoint D n
  disjoint D x
  disjoint k n
  disjoint m n
  disjoint n x
  disjoint D r
  disjoint r x
  disjoint F k
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F s
  disjoint G m
  disjoint H k
  disjoint H m
  disjoint H n
  disjoint I k
  disjoint I m
  disjoint I x
  disjoint I r
  disjoint M m
  disjoint P k
  disjoint P m
  disjoint P s
  disjoint P r
  disjoint S k
  disjoint S m
  disjoint S s
  disjoint Z k
  disjoint Z m
  disjoint Z n
  disjoint Z x
  disjoint k ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph r
  disjoint k x
  disjoint A i
  disjoint A j
  disjoint A z
  disjoint i j
  disjoint i k
  disjoint i m
  disjoint i s
  disjoint i z
  disjoint j k
  disjoint j m
  disjoint j s
  disjoint j z
  disjoint k z
  disjoint m z
  disjoint s z
  disjoint A y
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint k y
  disjoint m y
  disjoint x y
  disjoint C j
  disjoint D i
  disjoint D j
  disjoint i n
  disjoint j n
  disjoint D y
  disjoint i r
  disjoint r y
  disjoint F i
  disjoint F j
  disjoint F z
  disjoint n z
  disjoint x z
  disjoint F l
  disjoint i l
  disjoint l m
  disjoint l n
  disjoint G i
  disjoint G y
  disjoint H i
  disjoint H j
  disjoint I i
  disjoint I j
  disjoint I y
  disjoint P j
  disjoint S j
  disjoint Z i
  disjoint Z j
  disjoint Z z
  disjoint i ph
  disjoint j ph
  disjoint ph y
  assert |- ( ph -> ( D i^i I ) C_ { x e. D | ( G ` x ) <_ A } )

  proof
    wph
    vx
    cv
    #
    cG
    cfv
    #
    cA
    cle
    wbr
    #
    vx
    cD
    cD
    cI
    cin
    #
    @3
    cD
    wss
    wph
    cD
    cI
    inss1
    a1i
    #
    wph
    @0
    @3
    wcel
    #
    wa
    #
    @2
    @1
    cA
    vy
    cv
    #
    caddc
    co
    #
    cle
    wbr
    #
    vy
    crp
    wral
    #
    @6
    @9
    vy
    crp
    @6
    @7
    crp
    wcel
    #
    wa
    #
    @1
    @8
    @6
    @1
    cr
    wcel
    #
    @11
    wph
    @5
    @0
    cD
    wcel
    #
    @13
    wph
    @3
    cD
    @0
    @4
    sselda
    #
    wph
    @14
    wa
    #
    @1
    vm
    cZ
    @0
    vm
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
    cr
    wph
    vx
    cD
    @21
    cG
    cvv
    cG
    vx
    cD
    @21
    cmpt
    #
    wceq
    wph
    smflimlem4.6
    a1i
    @16
    @21
    cr
    @16
    vz
    cD
    vm
    vn
    cF
    cM
    @0
    cZ
    @16
    vm
    nfv
    vm
    cF
    nfcv
    vz
    cF
    nfcv
    smflimlem4.2
    wph
    @17
    cZ
    wcel
    #
    @18
    cdm
    #
    cr
    @18
    wf
    #
    @14
    wph
    @23
    wa
    #
    @24
    cS
    @18
    wph
    cS
    csalg
    wcel
    #
    @23
    smflimlem4.3
    adantr
    wph
    cZ
    cS
    csmblfn
    cfv
    #
    @17
    cF
    smflimlem4.4
    ffvelrnda
    #
    @24
    eqid
    smff
    #
    adantlr
    cD
    @20
    cli
    cdm
    #
    wcel
    #
    vx
    vn
    cZ
    vm
    vn
    cv
    #
    cuz
    cfv
    #
    @24
    ciin
    #
    ciun
    #
    crab
    #
    vm
    cZ
    vz
    cv
    #
    @18
    cfv
    #
    cmpt
    #
    @31
    wcel
    #
    vz
    @36
    crab
    smflimlem4.5
    @32
    @41
    vx
    vz
    @36
    @0
    @38
    wceq
    #
    @20
    @40
    @31
    @42
    vm
    cZ
    @19
    @39
    @0
    @38
    @18
    fveq2
    #
    mpteq2dv
    eleq1d
    cbvrabv
    eqtri
    #
    wph
    @14
    simpr
    fnlimfvre
    #
    elexd
    fvmpt2d
    @45
    eqeltrd
    syldan
    #
    adantr
    #
    wph
    @11
    @8
    cr
    wcel
    @5
    wph
    @11
    wa
    #
    cA
    @7
    wph
    cA
    cr
    wcel
    #
    @11
    smflimlem4.7
    adantr
    #
    @11
    @7
    cr
    wcel
    #
    wph
    @7
    rpre
    #
    adantl
    #
    readdcld
    adantlr
    @12
    @0
    @24
    wcel
    #
    @1
    @19
    @7
    c2
    cdiv
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    @19
    cA
    @55
    caddc
    co
    #
    clt
    wbr
    #
    w3a
    #
    vm
    cZ
    wrex
    #
    @1
    @8
    clt
    wbr
    #
    @12
    @54
    @59
    wa
    #
    @57
    wa
    #
    vm
    cZ
    wrex
    @61
    @12
    @1
    @0
    vi
    cv
    #
    cF
    cfv
    #
    cfv
    #
    @55
    caddc
    co
    #
    clt
    wbr
    #
    @0
    @66
    cdm
    #
    wcel
    #
    @67
    @58
    clt
    wbr
    #
    wa
    #
    @63
    @57
    vm
    vi
    cM
    cZ
    @12
    vm
    nfv
    #
    smflimlem4.2
    @12
    c1
    vk
    cv
    #
    cdiv
    co
    #
    @55
    clt
    wbr
    #
    vk
    cn
    wrex
    #
    @73
    vi
    @17
    cuz
    cfv
    #
    wral
    vm
    cZ
    wrex
    #
    @11
    @78
    @6
    @11
    @55
    crp
    wcel
    #
    @78
    @7
    rphalfcl
    #
    @55
    vk
    rpgtrecnn
    syl
    adantl
    @12
    @77
    @80
    vk
    cn
    @12
    @75
    cn
    wcel
    #
    @77
    @80
    @12
    @83
    wa
    #
    @77
    wa
    vz
    vr
    cA
    cC
    cD
    cP
    cS
    vi
    vj
    vm
    vn
    cF
    cH
    cI
    @75
    cM
    @0
    @55
    cZ
    vs
    smflimlem4.2
    wph
    @27
    @5
    @11
    @83
    @77
    smflimlem4.3
    ad4antr
    @6
    @23
    @18
    @28
    wcel
    #
    @11
    @83
    @77
    wph
    @23
    @85
    @5
    @29
    adantlr
    ad5ant15
    @44
    @6
    @49
    @11
    @83
    @77
    wph
    @49
    @5
    smflimlem4.7
    adantr
    #
    ad3antrrr
    cP
    vm
    vk
    cZ
    cn
    @19
    cA
    @76
    caddc
    co
    #
    clt
    wbr
    #
    vx
    @24
    crab
    #
    vs
    cv
    @24
    cin
    #
    wceq
    #
    vs
    cS
    crab
    #
    cmpt2
    vm
    vj
    cZ
    cn
    @39
    cA
    c1
    vj
    cv
    #
    cdiv
    co
    #
    caddc
    co
    #
    clt
    wbr
    #
    vz
    @24
    crab
    #
    @90
    wceq
    #
    vs
    cS
    crab
    #
    cmpt2
    smflimlem4.8
    vm
    vk
    vj
    cZ
    cn
    @92
    @99
    vk
    cZ
    nfcv
    #
    vj
    cZ
    nfcv
    #
    vj
    @92
    nfcv
    vk
    @99
    nfcv
    @75
    @93
    wceq
    #
    @91
    @98
    vs
    cS
    @102
    @89
    @97
    @90
    @102
    @89
    @39
    @87
    clt
    wbr
    #
    vz
    @24
    crab
    #
    @97
    @89
    @104
    wceq
    @102
    @88
    @103
    vx
    vz
    @24
    @42
    @19
    @39
    @87
    clt
    @43
    breq1d
    cbvrabv
    a1i
    @102
    @103
    @96
    vz
    @24
    @102
    @87
    @95
    @39
    clt
    @102
    @76
    @94
    cA
    caddc
    @75
    @93
    c1
    cdiv
    oveq2
    oveq2d
    breq2d
    rabbidv
    eqtrd
    eqeq1d
    rabbidv
    cbvmpt22
    eqtri
    cH
    vm
    vk
    cZ
    cn
    @17
    @75
    cP
    co
    #
    cC
    cfv
    #
    cmpt2
    vm
    vj
    cZ
    cn
    @17
    @93
    cP
    co
    #
    cC
    cfv
    #
    cmpt2
    smflimlem4.9
    vm
    vk
    vj
    cZ
    cn
    @106
    @108
    @100
    @101
    vj
    @106
    nfcv
    vk
    @108
    nfcv
    @102
    @105
    @107
    cC
    @75
    @93
    @17
    cP
    oveq2
    fveq2d
    cbvmpt22
    eqtri
    cI
    vk
    cn
    vn
    cZ
    vm
    @34
    @17
    @75
    cH
    co
    #
    ciin
    #
    ciun
    #
    ciin
    vj
    cn
    vn
    cZ
    vm
    @34
    @17
    @93
    cH
    co
    #
    ciin
    #
    ciun
    #
    ciin
    smflimlem4.10
    vk
    vj
    cn
    @111
    @114
    @102
    vn
    cZ
    @110
    @113
    @102
    @33
    cZ
    wcel
    #
    wa
    #
    vm
    @34
    @109
    @112
    @116
    @17
    @34
    wcel
    #
    wa
    @75
    @93
    @17
    cH
    @102
    @115
    @117
    simpll
    oveq2d
    iineq2dv
    iuneq2dv
    cbviinv
    eqtri
    @6
    vr
    cv
    #
    cP
    crn
    wcel
    #
    @118
    cC
    cfv
    @118
    wcel
    #
    @11
    @83
    @77
    wph
    @119
    @120
    @5
    smflimlem4.11
    adantlr
    ad5ant15
    wph
    @5
    @11
    @83
    @77
    simp-4r
    @12
    @83
    @77
    simplr
    @11
    @81
    @6
    @83
    @77
    @82
    ad3antlr
    @84
    @77
    simpr
    smflimlem3
    exp31
    rexlimdv
    mpd
    @12
    @67
    cr
    wcel
    #
    @67
    @1
    cmin
    co
    cabs
    cfv
    #
    @55
    clt
    wbr
    #
    wa
    #
    vi
    @79
    wral
    #
    vm
    cZ
    wrex
    @69
    vi
    @79
    wral
    #
    vm
    cZ
    wrex
    @12
    vx
    cD
    vi
    vm
    cF
    cG
    cM
    @0
    @55
    cZ
    @12
    vi
    nfv
    vi
    cF
    nfcv
    vx
    cF
    nfcv
    wph
    cM
    cz
    wcel
    @5
    @11
    smflimlem4.1
    ad2antrr
    smflimlem4.2
    wph
    @65
    cZ
    wcel
    #
    @70
    cr
    @66
    wf
    #
    @5
    @11
    @26
    @25
    wi
    wph
    @127
    wa
    #
    @128
    wi
    vm
    vi
    @17
    @65
    wceq
    #
    @26
    @129
    @25
    @128
    @130
    @23
    @127
    wph
    @17
    @65
    cZ
    eleq1
    anbi2d
    @130
    @24
    @70
    cr
    @18
    @66
    @17
    @65
    cF
    fveq2
    #
    @130
    @18
    @66
    @131
    dmeqd
    feq12d
    imbi12d
    @30
    chvarv
    ad4ant14
    cD
    @37
    @32
    vx
    vm
    cZ
    vi
    @79
    @70
    ciin
    #
    ciun
    #
    crab
    vi
    cZ
    @67
    cmpt
    #
    @31
    wcel
    #
    vx
    @133
    crab
    smflimlem4.5
    @32
    vx
    @36
    @133
    @36
    vn
    cZ
    vl
    @34
    vl
    cv
    #
    cF
    cfv
    #
    cdm
    #
    ciin
    #
    ciun
    @133
    vn
    cZ
    @35
    @139
    @35
    @139
    wceq
    @115
    vm
    vl
    @34
    @24
    @138
    @17
    @136
    wceq
    @18
    @137
    @17
    @136
    cF
    fveq2
    dmeqd
    cbviinv
    a1i
    iuneq2i
    vn
    vm
    cZ
    @139
    @132
    @33
    @17
    wceq
    #
    @139
    vl
    @79
    @138
    ciin
    #
    @132
    @140
    vl
    @34
    @79
    @138
    @33
    @17
    cuz
    fveq2
    iineq1d
    @141
    @132
    wceq
    @140
    vl
    vi
    @79
    @138
    @70
    @136
    @65
    wceq
    @137
    @66
    @136
    @65
    cF
    fveq2
    dmeqd
    cbviinv
    a1i
    eqtrd
    cbviunv
    eqtri
    rabeqi
    @32
    @135
    vx
    @133
    @20
    @134
    @31
    @134
    @20
    vi
    vm
    cZ
    @67
    @19
    @65
    @17
    wceq
    #
    @0
    @66
    @18
    @65
    @17
    cF
    fveq2
    #
    fveq1d
    #
    cbvmptv
    eqcomi
    #
    eleq1i
    rabbii
    3eqtri
    cG
    @22
    vx
    cD
    @134
    cli
    cfv
    #
    cmpt
    smflimlem4.6
    vx
    cD
    @21
    @146
    @20
    @134
    cli
    @145
    fveq2i
    mpteq2i
    eqtri
    @6
    @14
    @11
    @15
    adantr
    @11
    @81
    @6
    @82
    adantl
    fnlimabslt
    @12
    @125
    @126
    vm
    cZ
    @74
    @12
    @23
    @125
    @126
    wi
    @12
    @23
    wa
    #
    @124
    @69
    vi
    @79
    @12
    @124
    @69
    wi
    @23
    @65
    @79
    wcel
    @12
    @124
    @69
    @12
    @124
    wa
    #
    @1
    @67
    cmin
    co
    #
    @55
    clt
    wbr
    @69
    @148
    @149
    @149
    cabs
    cfv
    #
    @55
    @12
    @121
    @149
    cr
    wcel
    @123
    @12
    @121
    wa
    #
    @1
    @67
    @12
    @13
    @121
    @47
    adantr
    @12
    @121
    simpr
    resubcld
    #
    adantrr
    #
    @12
    @121
    @150
    cr
    wcel
    @123
    @151
    @149
    @151
    @149
    @152
    recnd
    abscld
    adantrr
    @11
    @55
    cr
    wcel
    #
    @6
    @124
    @11
    @7
    @52
    rehalfcld
    #
    ad2antlr
    #
    @148
    @149
    @153
    leabsd
    @6
    @124
    @150
    @55
    clt
    wbr
    @11
    @6
    @124
    wa
    @150
    @122
    @55
    clt
    @6
    @121
    @150
    @122
    wceq
    @123
    @6
    @121
    wa
    @1
    @67
    @6
    @1
    cc
    wcel
    @121
    @6
    @1
    @46
    recnd
    adantr
    @121
    @67
    cc
    wcel
    @6
    @67
    recn
    adantl
    abssubd
    adantrr
    @6
    @121
    @123
    simprr
    eqbrtrd
    adantlr
    lelttrd
    @148
    @1
    @67
    @55
    @12
    @13
    @124
    @47
    adantr
    @12
    @121
    @123
    simprl
    @156
    ltsubadd2d
    mpbid
    ex
    ad2antrr
    ralimdva
    ex
    reximdai
    mpd
    @142
    @71
    @54
    @72
    @59
    @142
    @70
    @24
    @0
    @142
    @66
    @18
    @143
    dmeqd
    eleq2d
    @142
    @67
    @19
    @58
    clt
    @144
    breq1d
    anbi12d
    @142
    @68
    @56
    @1
    clt
    @142
    @67
    @19
    @55
    caddc
    @144
    oveq1d
    breq2d
    rexanuz3
    @64
    @60
    vm
    cZ
    @64
    @54
    @59
    @57
    w3a
    @60
    @54
    @59
    @57
    df-3an
    @54
    @59
    @57
    3ancomb
    bitr3i
    rexbii
    sylib
    @12
    @60
    @62
    vm
    cZ
    @12
    @23
    @60
    @62
    @147
    @60
    wa
    #
    @1
    @58
    @55
    caddc
    co
    #
    @8
    clt
    @157
    @1
    @56
    @158
    @12
    @13
    @23
    @60
    @47
    ad2antrr
    @147
    @57
    @54
    @56
    cr
    wcel
    #
    @59
    wph
    @11
    @23
    @54
    @159
    @5
    @48
    @23
    wa
    #
    @54
    wa
    #
    @19
    @55
    wph
    @23
    @54
    @19
    cr
    wcel
    #
    @11
    wph
    @23
    @54
    w3a
    @24
    cr
    @0
    @18
    wph
    @23
    @25
    @54
    @30
    3adant3
    wph
    @23
    @54
    simp3
    ffvelrnd
    ad4ant134
    #
    @161
    @11
    @154
    wph
    @11
    @23
    @54
    simpllr
    @155
    syl
    #
    readdcld
    adantlllr
    3ad2antr1
    wph
    @11
    @158
    cr
    wcel
    @5
    @23
    @60
    @48
    @58
    @55
    @48
    @49
    @154
    wa
    @58
    cr
    wcel
    #
    @48
    @49
    @154
    @50
    @48
    @51
    @154
    @53
    @7
    rehalfcl
    syl
    #
    jca
    cA
    @55
    readdcl
    syl
    #
    @166
    readdcld
    ad5ant13
    @147
    @54
    @57
    @59
    simpr2
    @147
    @54
    @59
    @56
    @158
    clt
    wbr
    #
    @57
    wph
    @11
    @23
    @63
    @168
    @5
    @160
    @63
    wa
    @19
    @58
    @55
    @160
    @54
    @162
    @59
    @163
    adantrr
    @48
    @165
    @23
    @63
    @167
    ad2antrr
    @160
    @54
    @154
    @59
    @164
    adantrr
    @160
    @54
    @59
    simprr
    ltadd1dd
    adantlllr
    3adantr2
    lttrd
    wph
    @11
    @158
    @8
    wceq
    @5
    @23
    @60
    @48
    @158
    cA
    @55
    @55
    caddc
    co
    #
    caddc
    co
    #
    @8
    @48
    cA
    @55
    @55
    @48
    cA
    @50
    recnd
    @48
    @55
    @166
    recnd
    #
    @171
    addassd
    @11
    @170
    @8
    wceq
    wph
    @11
    @169
    @7
    cA
    caddc
    @11
    @7
    cc
    wcel
    @169
    @7
    wceq
    @11
    @7
    @52
    recnd
    @7
    2halves
    syl
    oveq2d
    adantl
    eqtrd
    ad5ant13
    breqtrd
    exp31
    rexlimdv
    mpd
    ltled
    ralrimiva
    @6
    @13
    @49
    @2
    @10
    wb
    @46
    @86
    vy
    @1
    cA
    alrple
    syl2anc
    mpbird
    ssrabdv
end
