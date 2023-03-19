include "cv.mm"
include "csb.mm"
include "cprod.mm"
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
include "prodeq1d.mm"
include "op1std.mm"
include "csbeq1d.mm"
include "op2ndd.mm"
include "csbeq2dv.mm"
include "eqtrd.mm"
include "cfn.mm"
include "snfi.mm"
include "adantr.mm"
include "wrex.mm"
include "opeliunxp2f.mm"
include "sylbbr.mm"
include "adantl.mm"
include "eleqtrrd.mm"
include "eliun.mm"
include "sylib.mm"
include "simpr.mm"
include "opelxp.mm"
include "simpld.mm"
include "elsni.mm"
include "syl.mm"
include "simpl.mm"
include "eqeltrd.mm"
include "rexlimiva.mm"
include "expr.mm"
include "ssrdv.mm"
include "ssfid.mm"
include "xpfi.mm"
include "sylancr.mm"
include "ralrimiva.mm"
include "iunfi.mm"
include "syl2anc.mm"
include "mprgbir.mm"
include "cc.mm"
include "xp2nd.mm"
include "xp1st.mm"
include "nfcri.mm"
include "wi.mm"
include "equcomd.mm"
include "eleq2d.mm"
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
include "fprodcnv.mm"
include "eqtr4d.mm"
include "fprod2d.mm"
include "3eqtr4d.mm"
include "nfcsb.mm"
include "nfcprod.mm"
include "cbvprodi.mm"
include "prodeq12dv.mm"
include "syl5eq.mm"
include "3eqtr4g.mm"

theorem fprodcom2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  assume fprodcom2.1: |- ( ph -> A e. Fin )
  assume fprodcom2.2: |- ( ph -> C e. Fin )
  assume fprodcom2.3: |- ( ( ph /\ j e. A ) -> B e. Fin )
  assume fprodcom2.4: |- ( ph -> ( ( j e. A /\ k e. B ) <-> ( k e. C /\ j e. D ) ) )
  assume fprodcom2.5: |- ( ( ph /\ ( j e. A /\ k e. B ) ) -> E e. CC )

  disjoint A j
  disjoint A k
  disjoint j k
  disjoint B k
  disjoint C j
  disjoint C k
  disjoint D j
  disjoint j ph
  disjoint k ph
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint j w
  disjoint k w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> prod_ j e. A prod_ k e. B E = prod_ k e. C prod_ j e. D E )

  proof
    wph
    cA
    vj
    vx
    cv
    #
    cB
    csb
    #
    vk
    vy
    cv
    #
    vj
    @0
    cE
    csb
    #
    csb
    #
    vy
    cprod
    #
    vx
    cprod
    #
    cC
    vk
    @2
    cD
    csb
    #
    @4
    vx
    cprod
    #
    vy
    cprod
    #
    cA
    cB
    cE
    vk
    cprod
    #
    vj
    cprod
    cC
    cD
    cE
    vj
    cprod
    #
    vk
    cprod
    wph
    vx
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
    cprod
    #
    vy
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
    cprod
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
    cprod
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
    @0
    @2
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
    @2
    @0
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
    @41
    @34
    wcel
    #
    @41
    @39
    wcel
    #
    wph
    @45
    @49
    vj
    vk
    wph
    @42
    @47
    @44
    @48
    @42
    @47
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
    @54
    @53
    wa
    @42
    @47
    @53
    @54
    ancom
    @0
    @2
    @31
    @35
    vx
    vex
    #
    vy
    vex
    #
    opth
    @2
    @0
    @35
    @31
    @56
    @55
    opth
    3bitr4i
    a1i
    fprodcom2.4
    anbi12d
    2exbidv
    vj
    vk
    cA
    cB
    @41
    eliunxp
    @52
    @46
    @38
    wcel
    #
    @49
    vj
    wex
    vk
    wex
    @50
    @0
    @2
    @38
    @55
    @56
    opelcnv
    #
    vk
    vj
    cC
    cD
    @46
    eliunxp
    @49
    vk
    vj
    excom
    3bitri
    3bitr4g
    eqrelrdv
    #
    vj
    vx
    cA
    @33
    @13
    vx
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
    vx
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
    vy
    cC
    @37
    @22
    vy
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
    vy
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
    prodeq1d
    wph
    vw
    vz
    @23
    @28
    @19
    @4
    vy
    vx
    @24
    @46
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
    @56
    @55
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
    @56
    @55
    op2ndd
    csbeq1d
    csbeq2dv
    eqtrd
    #
    @15
    @41
    wceq
    #
    @19
    vk
    @2
    @18
    csb
    @4
    @68
    vk
    @16
    @2
    @18
    @0
    @2
    @15
    @55
    @56
    op2ndd
    csbeq1d
    @68
    vk
    @2
    @18
    @3
    @68
    vj
    @17
    @0
    cE
    @0
    @2
    @15
    @55
    @56
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
    vy
    cC
    wral
    @23
    cfn
    wcel
    fprodcom2.2
    wph
    @70
    vy
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
    @70
    @2
    snfi
    @72
    cA
    @7
    wph
    cA
    cfn
    wcel
    @71
    fprodcom2.1
    adantr
    @72
    vx
    @7
    cA
    wph
    @71
    @0
    @7
    wcel
    #
    @0
    cA
    wcel
    #
    wph
    @71
    @73
    wa
    #
    wa
    #
    @41
    @33
    wcel
    #
    vj
    cA
    wrex
    #
    @74
    @76
    @51
    @78
    @76
    @41
    @39
    @34
    @75
    @52
    wph
    @52
    @57
    @75
    @58
    vk
    cC
    cD
    @2
    @0
    @7
    @63
    @65
    opeliunxp2f
    sylbbr
    adantl
    wph
    @34
    @39
    wceq
    @75
    @59
    adantr
    eleqtrrd
    vj
    @41
    cA
    @33
    eliun
    sylib
    #
    @77
    @74
    vj
    cA
    @43
    @77
    wa
    #
    @0
    @31
    cA
    @80
    @0
    @32
    wcel
    #
    @53
    @80
    @81
    @2
    cB
    wcel
    #
    @80
    @77
    @81
    @82
    wa
    #
    @43
    @77
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
    @43
    @77
    simpl
    eqeltrd
    rexlimiva
    syl
    #
    expr
    ssrdv
    ssfid
    #
    @21
    @7
    xpfi
    sylancr
    ralrimiva
    vy
    cC
    @22
    iunfi
    syl2anc
    @23
    wrel
    #
    wph
    @88
    @22
    wrel
    #
    vy
    cC
    vy
    cC
    @22
    reliun
    @89
    @71
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
    vx
    @92
    wral
    #
    @28
    cc
    wcel
    #
    @91
    @24
    @22
    wcel
    #
    vy
    cC
    wrex
    #
    @93
    @91
    @90
    @99
    wph
    @90
    simpr
    vy
    @24
    cC
    @22
    eliun
    sylib
    #
    @98
    @93
    vy
    cC
    @71
    @98
    wa
    #
    @26
    @7
    @92
    @98
    @26
    @7
    wcel
    @71
    @24
    @21
    @7
    xp2nd
    adantl
    @101
    vk
    @25
    @2
    cD
    @101
    @25
    @21
    wcel
    #
    @25
    @2
    wceq
    @98
    @102
    @71
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
    @91
    @25
    cC
    wcel
    #
    @4
    cc
    wcel
    #
    vx
    @7
    wral
    #
    vy
    cC
    wral
    #
    @96
    @91
    @99
    @104
    @100
    @98
    @104
    vy
    cC
    @101
    @25
    @2
    cC
    @103
    @71
    @98
    simpl
    eqeltrd
    rexlimiva
    syl
    wph
    @107
    @90
    wph
    @105
    vy
    vx
    cC
    @7
    @76
    wph
    @74
    @2
    @1
    wcel
    #
    @105
    wph
    @75
    simpl
    @86
    @76
    @78
    @108
    @79
    @77
    @108
    vj
    cA
    vj
    vy
    @1
    @60
    nfcri
    @77
    @108
    wi
    @43
    @77
    @83
    @108
    @84
    @81
    @82
    @108
    @81
    cB
    @1
    @2
    @81
    @61
    cB
    @1
    wceq
    @81
    vx
    vj
    @85
    equcomd
    @62
    syl
    eleq2d
    biimpa
    sylbi
    a1i
    rexlimi
    syl
    wph
    @74
    @108
    @105
    wph
    @74
    wa
    @3
    cc
    wcel
    #
    vk
    @1
    wral
    #
    @108
    @105
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
    @74
    @110
    wph
    @111
    vj
    vk
    cA
    cB
    fprodcom2.5
    ralrimivva
    @112
    @110
    vj
    @0
    cA
    @109
    vj
    vk
    @1
    @60
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
    @61
    @111
    @109
    vk
    cB
    @1
    @62
    @61
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
    @109
    @105
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
    @64
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
    @106
    @96
    vy
    @25
    cC
    @2
    @25
    wceq
    #
    @105
    @95
    vx
    @7
    @92
    vk
    @2
    @25
    cD
    csbeq1
    @119
    @4
    @94
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
    @95
    @97
    vx
    @26
    @92
    @0
    @26
    wceq
    #
    @94
    @28
    cc
    @120
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
    fprodcnv
    eqtr4d
    wph
    vz
    cA
    @1
    @4
    @19
    vx
    vy
    @69
    fprodcom2.1
    wph
    cB
    cfn
    wcel
    #
    vj
    cA
    wral
    @74
    @1
    cfn
    wcel
    #
    wph
    @121
    vj
    cA
    fprodcom2.3
    ralrimiva
    @121
    @122
    vj
    @0
    cA
    vj
    @1
    cfn
    @60
    nfel1
    @61
    cB
    @1
    cfn
    @62
    eleq1d
    rspc
    mpan9
    @117
    fprod2d
    wph
    vw
    cC
    @7
    @4
    @28
    vy
    vx
    @67
    fprodcom2.2
    @87
    @118
    fprod2d
    3eqtr4d
    cA
    @10
    @5
    vj
    vx
    vx
    @10
    nfcv
    vj
    @1
    @4
    vy
    @60
    vj
    vk
    @2
    @3
    vj
    @2
    nfcv
    @113
    nfcsb
    nfcprod
    @61
    @10
    cB
    vk
    @2
    cE
    csb
    #
    vy
    cprod
    @5
    cB
    cE
    @123
    vk
    vy
    vy
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
    cbvprodi
    @61
    cB
    @1
    @123
    @4
    vy
    @62
    @61
    @123
    @4
    wceq
    @82
    @61
    vk
    @2
    cE
    @3
    @114
    csbeq2dv
    adantr
    prodeq12dv
    syl5eq
    cbvprodi
    cC
    @11
    @8
    vk
    vy
    vy
    @11
    nfcv
    vk
    @7
    @4
    vx
    @63
    @115
    nfcprod
    @64
    @11
    cD
    @3
    vx
    cprod
    @8
    cD
    cE
    @3
    vj
    vx
    vx
    cE
    nfcv
    @113
    @114
    cbvprodi
    @64
    cD
    @7
    @3
    @4
    vx
    @65
    @64
    @3
    @4
    wceq
    @0
    cD
    wcel
    @116
    adantr
    prodeq12dv
    syl5eq
    cbvprodi
    3eqtr4g
end
