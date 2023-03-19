include "cv.mm"
include "csb.mm"
include "csu.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "c2nd.mm"
include "cfv.mm"
include "c1st.mm"
include "ccnv.mm"
include "wrel.mm"
include "wral.mm"
include "relxp.mm"
include "rgenw.mm"
include "reliun.mm"
include "mpbir.mm"
include "relcnv.mm"
include "cop.mm"
include "wceq.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wb.mm"
include "weq.mm"
include "ancom.mm"
include "vex.mm"
include "opth.mm"
include "3bitr4i.mm"
include "a1i.mm"
include "anbi12d.mm"
include "2exbidv.mm"
include "eliunxp.mm"
include "opelcnv.mm"
include "excom.mm"
include "3bitri.mm"
include "3bitr4g.mm"
include "eqrelrdv.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfxp.mm"
include "sneq.mm"
include "csbeq1a.mm"
include "xpeq12d.mm"
include "cbviun.mm"
include "cnveqi.mm"
include "3eqtr3g.mm"
include "sumeq1d.mm"
include "op1std.mm"
include "csbeq1d.mm"
include "op2ndd.mm"
include "csbeq2dv.mm"
include "eqtrd.mm"
include "cfn.mm"
include "snfi.mm"
include "wss.mm"
include "adantr.mm"
include "wrex.mm"
include "nfcri.mm"
include "id.mm"
include "vsnid.mm"
include "syl6eqelr.mm"
include "biantrurd.mm"
include "opelxp.mm"
include "syl6rbbr.mm"
include "eleq2d.mm"
include "bitrd.mm"
include "rspce.mm"
include "eliun.mm"
include "sylibr.mm"
include "adantl.mm"
include "eleqtrrd.mm"
include "sylib.mm"
include "simpr.mm"
include "simpld.mm"
include "elsni.mm"
include "syl.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "rexlimiva.mm"
include "expr.mm"
include "ssrdv.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "xpfi.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "iunfi.mm"
include "mprgbir.mm"
include "cc.mm"
include "xp2nd.mm"
include "xp1st.mm"
include "wi.mm"
include "eqcomd.mm"
include "biimpa.mm"
include "sylbi.mm"
include "rexlimi.mm"
include "ralrimivva.mm"
include "nfel1.mm"
include "nfral.mm"
include "eleq1d.mm"
include "raleqbidv.mm"
include "rspc.mm"
include "mpan9.mm"
include "syl5com.mm"
include "impr.mm"
include "syl12anc.mm"
include "csbeq1.mm"
include "rspcv.mm"
include "sylc.mm"
include "fsumcnv.mm"
include "eqtr4d.mm"
include "fsum2d.mm"
include "3eqtr4d.mm"
include "nfcsb.mm"
include "nfsum.mm"
include "cbvsumi.mm"
include "sumeq12dv.mm"
include "syl5eq.mm"
include "3eqtr4g.mm"

theorem fsumcom2OLD
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume fsumcom2.1: |- ( ph -> A e. Fin )
  assume fsumcom2.2: |- ( ph -> C e. Fin )
  assume fsumcom2.3: |- ( ( ph /\ j e. A ) -> B e. Fin )
  assume fsumcom2.4: |- ( ph -> ( ( j e. A /\ k e. B ) <-> ( k e. C /\ j e. D ) ) )
  assume fsumcom2.5: |- ( ( ph /\ ( j e. A /\ k e. B ) ) -> E e. CC )

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint C j
  disjoint C k
  disjoint j ph
  disjoint k ph
  disjoint B k
  disjoint D j
  disjoint j m
  disjoint j n
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint j w
  disjoint k w
  disjoint m w
  disjoint C m
  disjoint n w
  disjoint C n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint m ph
  disjoint n ph
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint B m
  disjoint B n
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint D m
  disjoint D n
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E m
  disjoint E n
  disjoint E w
  disjoint E z
  assert |- ( ph -> sum_ j e. A sum_ k e. B E = sum_ k e. C sum_ j e. D E )

  proof
    wph
    cA
    vj
    vm
    cv
    #
    cB
    csb
    #
    vk
    vn
    cv
    #
    vj
    @0
    cE
    csb
    #
    csb
    #
    vn
    csu
    #
    vm
    csu
    #
    cC
    vk
    @2
    cD
    csb
    #
    @4
    vm
    csu
    #
    vn
    csu
    #
    cA
    cB
    cE
    vk
    csu
    #
    vj
    csu
    cC
    cD
    cE
    vj
    csu
    #
    vk
    csu
    wph
    vm
    cA
    @0
    csn
    #
    @1
    cxp
    #
    ciun
    #
    vk
    vz
    cv
    #
    c2nd
    cfv
    #
    vj
    @15
    c1st
    cfv
    #
    cE
    csb
    #
    csb
    #
    vz
    csu
    #
    vn
    cC
    @2
    csn
    #
    @7
    cxp
    #
    ciun
    #
    vk
    vw
    cv
    #
    c1st
    cfv
    #
    vj
    @24
    c2nd
    cfv
    #
    cE
    csb
    #
    csb
    #
    vw
    csu
    #
    @6
    @9
    wph
    @20
    @23
    ccnv
    #
    @19
    vz
    csu
    @29
    wph
    @14
    @30
    @19
    vz
    wph
    vj
    cA
    vj
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    #
    vk
    cC
    vk
    cv
    #
    csn
    #
    cD
    cxp
    #
    ciun
    #
    ccnv
    #
    @14
    @30
    wph
    vx
    vy
    @34
    @39
    @34
    wrel
    @33
    wrel
    #
    vj
    cA
    wral
    @40
    vj
    cA
    @32
    cB
    relxp
    rgenw
    vj
    cA
    @33
    reliun
    mpbir
    @38
    relcnv
    wph
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @31
    @35
    cop
    wceq
    #
    @31
    cA
    wcel
    #
    @35
    cB
    wcel
    wa
    #
    wa
    #
    vk
    wex
    vj
    wex
    @42
    @41
    cop
    #
    @35
    @31
    cop
    wceq
    #
    @35
    cC
    wcel
    @31
    cD
    wcel
    wa
    #
    wa
    #
    vk
    wex
    vj
    wex
    #
    @43
    @34
    wcel
    @43
    @39
    wcel
    #
    wph
    @47
    @51
    vj
    vk
    wph
    @44
    @49
    @46
    @50
    @44
    @49
    wb
    wph
    vx
    vj
    weq
    #
    vy
    vk
    weq
    #
    wa
    @55
    @54
    wa
    @44
    @49
    @54
    @55
    ancom
    @41
    @42
    @31
    @35
    vx
    vex
    #
    vy
    vex
    #
    opth
    @42
    @41
    @35
    @31
    @57
    @56
    opth
    3bitr4i
    a1i
    fsumcom2.4
    anbi12d
    2exbidv
    vj
    vk
    cA
    cB
    @43
    eliunxp
    @53
    @48
    @38
    wcel
    @51
    vj
    wex
    vk
    wex
    @52
    @41
    @42
    @38
    @56
    @57
    opelcnv
    vk
    vj
    cC
    cD
    @48
    eliunxp
    @51
    vk
    vj
    excom
    3bitri
    3bitr4g
    eqrelrdv
    #
    vj
    vm
    cA
    @33
    @13
    vm
    @33
    nfcv
    vj
    @12
    @1
    vj
    @12
    nfcv
    vj
    @0
    cB
    nfcsb1v
    #
    nfxp
    vj
    vm
    weq
    #
    @32
    @12
    cB
    @1
    @31
    @0
    sneq
    vj
    @0
    cB
    csbeq1a
    #
    xpeq12d
    cbviun
    @38
    @23
    vk
    vn
    cC
    @37
    @22
    vn
    @37
    nfcv
    vk
    @21
    @7
    vk
    @21
    nfcv
    vk
    @2
    cD
    nfcsb1v
    #
    nfxp
    vk
    vn
    weq
    #
    @36
    @21
    cD
    @7
    @35
    @2
    sneq
    vk
    @2
    cD
    csbeq1a
    #
    xpeq12d
    cbviun
    cnveqi
    3eqtr3g
    sumeq1d
    wph
    vw
    vz
    @23
    @28
    @19
    @4
    vn
    vm
    @24
    @2
    @0
    cop
    #
    wceq
    #
    @28
    vk
    @2
    @27
    csb
    @4
    @66
    vk
    @25
    @2
    @27
    @2
    @0
    @24
    vn
    vex
    #
    vm
    vex
    #
    op1std
    csbeq1d
    @66
    vk
    @2
    @27
    @3
    @66
    vj
    @26
    @0
    cE
    @2
    @0
    @24
    @67
    @68
    op2ndd
    csbeq1d
    csbeq2dv
    eqtrd
    #
    @15
    @0
    @2
    cop
    #
    wceq
    #
    @19
    vk
    @2
    @18
    csb
    @4
    @71
    vk
    @16
    @2
    @18
    @0
    @2
    @15
    @68
    @67
    op2ndd
    csbeq1d
    @71
    vk
    @2
    @18
    @3
    @71
    vj
    @17
    @0
    cE
    @0
    @2
    @15
    @68
    @67
    op1std
    csbeq1d
    csbeq2dv
    eqtrd
    #
    wph
    cC
    cfn
    wcel
    @22
    cfn
    wcel
    #
    vn
    cC
    wral
    @23
    cfn
    wcel
    fsumcom2.2
    wph
    @73
    vn
    cC
    wph
    @2
    cC
    wcel
    #
    wa
    #
    @21
    cfn
    wcel
    @7
    cfn
    wcel
    #
    @73
    @2
    snfi
    @75
    cA
    cfn
    wcel
    #
    @7
    cA
    wss
    @76
    wph
    @77
    @74
    fsumcom2.1
    adantr
    @75
    vm
    @7
    cA
    wph
    @74
    @0
    @7
    wcel
    #
    @0
    cA
    wcel
    #
    wph
    @74
    @78
    wa
    #
    wa
    #
    @70
    @33
    wcel
    #
    vj
    cA
    wrex
    #
    @79
    @81
    @70
    @34
    wcel
    @83
    @81
    @70
    @39
    @34
    @80
    @70
    @39
    wcel
    #
    wph
    @80
    @65
    @38
    wcel
    #
    @84
    @80
    @65
    @37
    wcel
    #
    vk
    cC
    wrex
    @85
    @86
    @78
    vk
    @2
    cC
    vk
    vm
    @7
    @62
    nfcri
    @63
    @86
    @0
    cD
    wcel
    #
    @78
    @63
    @87
    @2
    @36
    wcel
    #
    @87
    wa
    @86
    @63
    @88
    @87
    @63
    @2
    @35
    @36
    @63
    id
    vk
    vsnid
    syl6eqelr
    biantrurd
    @2
    @0
    @36
    cD
    opelxp
    syl6rbbr
    @63
    cD
    @7
    @0
    @64
    eleq2d
    bitrd
    rspce
    vk
    @65
    cC
    @37
    eliun
    sylibr
    @0
    @2
    @38
    @68
    @67
    opelcnv
    sylibr
    adantl
    wph
    @34
    @39
    wceq
    @80
    @58
    adantr
    eleqtrrd
    vj
    @70
    cA
    @33
    eliun
    sylib
    #
    @82
    @79
    vj
    cA
    @45
    @82
    wa
    #
    @0
    @31
    cA
    @90
    @0
    @32
    wcel
    #
    vm
    vj
    weq
    @90
    @91
    @2
    cB
    wcel
    #
    @90
    @82
    @91
    @92
    wa
    #
    @45
    @82
    simpr
    @0
    @2
    @32
    cB
    opelxp
    #
    sylib
    simpld
    @0
    @31
    elsni
    #
    syl
    @45
    @82
    simpl
    eqeltrd
    rexlimiva
    syl
    #
    expr
    ssrdv
    cA
    @7
    ssfi
    syl2anc
    #
    @21
    @7
    xpfi
    sylancr
    ralrimiva
    vn
    cC
    @22
    iunfi
    syl2anc
    @23
    wrel
    #
    wph
    @98
    @22
    wrel
    #
    vn
    cC
    vn
    cC
    @22
    reliun
    @99
    @74
    @21
    @7
    relxp
    a1i
    mprgbir
    a1i
    wph
    @24
    @23
    wcel
    #
    wa
    #
    @26
    vk
    @25
    cD
    csb
    #
    wcel
    #
    vk
    @25
    @3
    csb
    #
    cc
    wcel
    #
    vm
    @102
    wral
    #
    @28
    cc
    wcel
    #
    @101
    @24
    @22
    wcel
    #
    vn
    cC
    wrex
    #
    @103
    @101
    @100
    @109
    wph
    @100
    simpr
    vn
    @24
    cC
    @22
    eliun
    sylib
    #
    @108
    @103
    vn
    cC
    @74
    @108
    wa
    #
    @26
    @7
    @102
    @108
    @26
    @7
    wcel
    @74
    @24
    @21
    @7
    xp2nd
    adantl
    @111
    vk
    @25
    @2
    cD
    @111
    @25
    @21
    wcel
    #
    @25
    @2
    wceq
    @108
    @112
    @74
    @24
    @21
    @7
    xp1st
    adantl
    @25
    @2
    elsni
    syl
    #
    csbeq1d
    eleqtrrd
    rexlimiva
    syl
    @101
    @25
    cC
    wcel
    #
    @4
    cc
    wcel
    #
    vm
    @7
    wral
    #
    vn
    cC
    wral
    #
    @106
    @101
    @109
    @114
    @110
    @108
    @114
    vn
    cC
    @111
    @25
    @2
    cC
    @113
    @74
    @108
    simpl
    eqeltrd
    rexlimiva
    syl
    wph
    @117
    @100
    wph
    @115
    vn
    vm
    cC
    @7
    @81
    wph
    @79
    @2
    @1
    wcel
    #
    @115
    wph
    @80
    simpl
    @96
    @81
    @83
    @118
    @89
    @82
    @118
    vj
    cA
    vj
    vn
    @1
    @59
    nfcri
    @82
    @118
    wi
    @45
    @82
    @93
    @118
    @94
    @91
    @92
    @118
    @91
    cB
    @1
    @2
    @91
    @60
    cB
    @1
    wceq
    @91
    @0
    @31
    @95
    eqcomd
    @61
    syl
    eleq2d
    biimpa
    sylbi
    a1i
    rexlimi
    syl
    wph
    @79
    @118
    @115
    wph
    @79
    wa
    @3
    cc
    wcel
    #
    vk
    @1
    wral
    #
    @118
    @115
    wph
    cE
    cc
    wcel
    #
    vk
    cB
    wral
    #
    vj
    cA
    wral
    @79
    @120
    wph
    @121
    vj
    vk
    cA
    cB
    fsumcom2.5
    ralrimivva
    @122
    @120
    vj
    @0
    cA
    @119
    vj
    vk
    @1
    @59
    vj
    @3
    cc
    vj
    @0
    cE
    nfcsb1v
    #
    nfel1
    nfral
    @60
    @121
    @119
    vk
    cB
    @1
    @61
    @60
    cE
    @3
    cc
    vj
    @0
    cE
    csbeq1a
    #
    eleq1d
    raleqbidv
    rspc
    mpan9
    @119
    @115
    vk
    @2
    @1
    vk
    @4
    cc
    vk
    @2
    @3
    nfcsb1v
    #
    nfel1
    @63
    @3
    @4
    cc
    vk
    @2
    @3
    csbeq1a
    #
    eleq1d
    rspc
    syl5com
    impr
    #
    syl12anc
    #
    ralrimivva
    adantr
    @116
    @106
    vn
    @25
    cC
    @2
    @25
    wceq
    #
    @115
    @105
    vm
    @7
    @102
    vk
    @2
    @25
    cD
    csbeq1
    @129
    @4
    @104
    cc
    vk
    @2
    @25
    @3
    csbeq1
    eleq1d
    raleqbidv
    rspcv
    sylc
    @105
    @107
    vm
    @26
    @102
    @0
    @26
    wceq
    #
    @104
    @28
    cc
    @130
    vk
    @25
    @3
    @27
    vj
    @0
    @26
    cE
    csbeq1
    csbeq2dv
    eleq1d
    rspcv
    sylc
    fsumcnv
    eqtr4d
    wph
    vz
    cA
    @1
    @4
    @19
    vm
    vn
    @72
    fsumcom2.1
    wph
    cB
    cfn
    wcel
    #
    vj
    cA
    wral
    @79
    @1
    cfn
    wcel
    #
    wph
    @131
    vj
    cA
    fsumcom2.3
    ralrimiva
    @131
    @132
    vj
    @0
    cA
    vj
    @1
    cfn
    @59
    nfel1
    @60
    cB
    @1
    cfn
    @61
    eleq1d
    rspc
    mpan9
    @127
    fsum2d
    wph
    vw
    cC
    @7
    @4
    @28
    vn
    vm
    @69
    fsumcom2.2
    @97
    @128
    fsum2d
    3eqtr4d
    cA
    @10
    @5
    vj
    vm
    vm
    @10
    nfcv
    vj
    @1
    @4
    vn
    @59
    vj
    vk
    @2
    @3
    vj
    @2
    nfcv
    @123
    nfcsb
    nfsum
    @60
    @10
    cB
    vk
    @2
    cE
    csb
    #
    vn
    csu
    @5
    cB
    cE
    @133
    vk
    vn
    vn
    cE
    nfcv
    vk
    @2
    cE
    nfcsb1v
    vk
    @2
    cE
    csbeq1a
    cbvsumi
    @60
    cB
    @1
    @133
    @4
    vn
    @61
    @60
    @133
    @4
    wceq
    @92
    @60
    vk
    @2
    cE
    @3
    @124
    csbeq2dv
    adantr
    sumeq12dv
    syl5eq
    cbvsumi
    cC
    @11
    @8
    vk
    vn
    vn
    @11
    nfcv
    vk
    @7
    @4
    vm
    @62
    @125
    nfsum
    @63
    @11
    cD
    @3
    vm
    csu
    @8
    cD
    cE
    @3
    vj
    vm
    vm
    cE
    nfcv
    @123
    @124
    cbvsumi
    @63
    cD
    @7
    @3
    @4
    vm
    @64
    @63
    @3
    @4
    wceq
    @87
    @126
    adantr
    sumeq12dv
    syl5eq
    cbvsumi
    3eqtr4g
end
