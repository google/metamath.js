include "wceq.mm"
include "cfzo.mm"
include "co.mm"
include "cmin.mm"
include "cmul.mm"
include "csu.mm"
include "c1.mm"
include "caddc.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "cc0.mm"
include "sum0.mm"
include "0m0e0.mm"
include "eqtr4i.mm"
include "simpr.mm"
include "oveq2d.mm"
include "fzo0.mm"
include "syl6eq.mm"
include "sumeq1d.mm"
include "cfz.mm"
include "eluzfz1.mm"
include "syl.mm"
include "wi.mm"
include "cv.mm"
include "eqtr3.mm"
include "oveq12.mm"
include "3syl.mm"
include "adantr.mm"
include "eqeq12d.mm"
include "pm5.74da.mm"
include "eqidd.mm"
include "vtoclg.mm"
include "imp.mm"
include "sylan.mm"
include "oveq1d.mm"
include "cc.mm"
include "wral.mm"
include "ralrimiva.mm"
include "simpld.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "simprd.mm"
include "mulcld.mm"
include "subidd.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "3eqtr4a.mm"
include "cz.mm"
include "wss.mm"
include "eluzel2.mm"
include "fzp1ss.mm"
include "sselda.mm"
include "adantlr.mm"
include "syldan.mm"
include "fsumm1.mm"
include "eluzelz.mm"
include "fzoval.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "eqtr4d.mm"
include "1zzd.mm"
include "peano2zd.mm"
include "fsumshftm.mm"
include "3eqtr4d.mm"
include "cfn.mm"
include "fzofi.mm"
include "a1i.mm"
include "uzid.mm"
include "peano2uz.mm"
include "fzoss1.mm"
include "4syl.mm"
include "elfzofz.mm"
include "sylan2.mm"
include "fsumcl.mm"
include "eluzfz2.mm"
include "addcomd.mm"
include "fzofzp1.mm"
include "rspccva.mm"
include "syl2an.mm"
include "subdird.mm"
include "sumeq2dv.mm"
include "fsumsub.mm"
include "subsub3d.mm"
include "subcld.mm"
include "nnncan1d.mm"
include "eluzp1m1.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "fsum1p.mm"
include "cbvsumv.mm"
include "subsub4d.mm"
include "subdid.mm"
include "3eqtrrd.mm"
include "wo.mm"
include "uzp1.mm"
include "mpjaodan.mm"

theorem fsumparts
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume fsumparts.b: |- ( k = j -> ( A = B /\ V = W ) )
  assume fsumparts.c: |- ( k = ( j + 1 ) -> ( A = C /\ V = X ) )
  assume fsumparts.d: |- ( k = M -> ( A = D /\ V = Y ) )
  assume fsumparts.e: |- ( k = N -> ( A = E /\ V = Z ) )
  assume fsumparts.1: |- ( ph -> N e. ( ZZ>= ` M ) )
  assume fsumparts.2: |- ( ( ph /\ k e. ( M ... N ) ) -> A e. CC )
  assume fsumparts.3: |- ( ( ph /\ k e. ( M ... N ) ) -> V e. CC )

  disjoint A j
  disjoint B k
  disjoint C k
  disjoint D k
  disjoint E k
  disjoint V j
  disjoint W k
  disjoint j k
  disjoint M j
  disjoint M k
  disjoint N j
  disjoint N k
  disjoint j ph
  disjoint k ph
  disjoint X k
  disjoint Y k
  disjoint Z k
  assert |- ( ph -> sum_ j e. ( M ..^ N ) ( B x. ( X - W ) ) = ( ( ( E x. Z ) - ( D x. Y ) ) - sum_ j e. ( M ..^ N ) ( ( C - B ) x. X ) ) )

  proof
    wph
    cN
    cM
    wceq
    #
    cM
    cN
    cfzo
    co
    #
    cB
    cX
    cW
    cmin
    co
    cmul
    co
    #
    vj
    csu
    #
    cE
    cZ
    cmul
    co
    #
    cD
    cY
    cmul
    co
    #
    cmin
    co
    #
    @1
    cC
    cB
    cmin
    co
    cX
    cmul
    co
    #
    vj
    csu
    #
    cmin
    co
    #
    wceq
    cN
    cM
    c1
    caddc
    co
    #
    cuz
    cfv
    wcel
    #
    wph
    @0
    wa
    #
    c0
    @2
    vj
    csu
    #
    cc0
    cc0
    cmin
    co
    #
    @3
    @9
    @13
    cc0
    @14
    @2
    vj
    sum0
    0m0e0
    eqtr4i
    @12
    @1
    c0
    @2
    vj
    @12
    @1
    cM
    cM
    cfzo
    co
    c0
    @12
    cN
    cM
    cM
    cfzo
    wph
    @0
    simpr
    oveq2d
    cM
    fzo0
    syl6eq
    #
    sumeq1d
    @12
    @6
    cc0
    @8
    cc0
    cmin
    @12
    @6
    @5
    @5
    cmin
    co
    #
    cc0
    @12
    @4
    @5
    @5
    cmin
    wph
    cM
    cM
    cN
    cfz
    co
    #
    wcel
    #
    @0
    @4
    @5
    wceq
    #
    wph
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @18
    fsumparts.1
    cM
    cN
    eluzfz1
    syl
    #
    @18
    @0
    @19
    @0
    cA
    cV
    cmul
    co
    #
    @23
    wceq
    #
    wi
    @0
    @19
    wi
    vk
    cM
    @17
    vk
    cv
    #
    cM
    wceq
    #
    @0
    @24
    @19
    @26
    @0
    wa
    #
    @23
    @4
    @23
    @5
    @27
    @25
    cN
    wceq
    #
    cA
    cE
    wceq
    #
    cV
    cZ
    wceq
    #
    wa
    #
    @23
    @4
    wceq
    #
    @25
    cN
    cM
    eqtr3
    fsumparts.e
    cA
    cE
    cV
    cZ
    cmul
    oveq12
    #
    3syl
    @26
    @23
    @5
    wceq
    #
    @0
    @26
    cA
    cD
    wceq
    #
    cV
    cY
    wceq
    #
    wa
    @34
    fsumparts.d
    cA
    cD
    cV
    cY
    cmul
    oveq12
    syl
    #
    adantr
    eqeq12d
    pm5.74da
    @0
    @23
    eqidd
    vtoclg
    imp
    sylan
    oveq1d
    wph
    @16
    cc0
    wceq
    @0
    wph
    @5
    wph
    cD
    cY
    wph
    @18
    cA
    cc
    wcel
    #
    vk
    @17
    wral
    #
    cD
    cc
    wcel
    #
    @22
    wph
    @38
    vk
    @17
    fsumparts.2
    ralrimiva
    #
    @38
    @40
    vk
    cM
    @17
    @26
    cA
    cD
    cc
    @26
    @35
    @36
    fsumparts.d
    simpld
    eleq1d
    rspcv
    sylc
    wph
    @18
    cV
    cc
    wcel
    #
    vk
    @17
    wral
    #
    cY
    cc
    wcel
    #
    @22
    wph
    @42
    vk
    @17
    fsumparts.3
    ralrimiva
    #
    @42
    @44
    vk
    cM
    @17
    @26
    cV
    cY
    cc
    @26
    @35
    @36
    fsumparts.d
    simprd
    eleq1d
    rspcv
    sylc
    mulcld
    #
    subidd
    adantr
    eqtrd
    @12
    @8
    c0
    @7
    vj
    csu
    cc0
    @12
    @1
    c0
    @7
    vj
    @15
    sumeq1d
    @7
    vj
    sum0
    syl6eq
    oveq12d
    3eqtr4a
    wph
    @11
    wa
    #
    @9
    @6
    @4
    @1
    cB
    cX
    cmul
    co
    #
    vj
    csu
    #
    @10
    cN
    cfzo
    co
    #
    @23
    vk
    csu
    #
    cmin
    co
    #
    cmin
    co
    #
    cmin
    co
    @52
    @5
    cmin
    co
    #
    @3
    @47
    @8
    @53
    @6
    cmin
    @47
    @1
    cC
    cX
    cmul
    co
    #
    vj
    csu
    #
    @49
    cmin
    co
    #
    @4
    @51
    caddc
    co
    #
    @49
    cmin
    co
    @8
    @53
    @47
    @56
    @58
    @49
    cmin
    @47
    @56
    @51
    @4
    caddc
    co
    #
    @58
    @47
    @10
    cN
    cfz
    co
    #
    @23
    vk
    csu
    #
    @10
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    @23
    vk
    csu
    #
    @4
    caddc
    co
    @56
    @59
    @47
    @23
    @4
    vk
    @10
    cN
    wph
    @11
    simpr
    @47
    @25
    @60
    wcel
    @25
    @17
    wcel
    #
    @23
    cc
    wcel
    #
    @47
    @60
    @17
    @25
    @47
    cM
    cz
    wcel
    #
    @60
    @17
    wss
    wph
    @67
    @11
    wph
    @21
    @67
    fsumparts.1
    cM
    cN
    eluzel2
    syl
    #
    adantr
    #
    cM
    cN
    fzp1ss
    syl
    sselda
    wph
    @65
    @66
    @11
    wph
    @65
    wa
    cA
    cV
    fsumparts.2
    fsumparts.3
    mulcld
    #
    adantlr
    syldan
    #
    @28
    @31
    @32
    fsumparts.e
    @33
    syl
    fsumm1
    @47
    @56
    @10
    c1
    cmin
    co
    #
    @62
    cfz
    co
    #
    @55
    vj
    csu
    @61
    @47
    @1
    @73
    @55
    vj
    @47
    @1
    cM
    @62
    cfz
    co
    #
    @73
    @47
    cN
    cz
    wcel
    #
    @1
    @74
    wceq
    wph
    @75
    @11
    wph
    @21
    @75
    fsumparts.1
    cM
    cN
    eluzelz
    syl
    adantr
    #
    cM
    cN
    fzoval
    syl
    #
    @47
    @72
    cM
    @62
    cfz
    @47
    cM
    cc
    wcel
    c1
    cc
    wcel
    @72
    cM
    wceq
    @47
    cM
    @69
    zcnd
    ax-1cn
    cM
    c1
    pncan
    sylancl
    oveq1d
    eqtr4d
    sumeq1d
    @47
    @23
    @55
    vk
    vj
    c1
    @10
    cN
    @47
    1zzd
    @47
    cM
    @69
    peano2zd
    @76
    @71
    @25
    vj
    cv
    #
    c1
    caddc
    co
    #
    wceq
    #
    cA
    cC
    wceq
    #
    cV
    cX
    wceq
    #
    wa
    @23
    @55
    wceq
    fsumparts.c
    cA
    cC
    cV
    cX
    cmul
    oveq12
    syl
    fsumshftm
    eqtr4d
    @47
    @51
    @64
    @4
    caddc
    @47
    @50
    @63
    @23
    vk
    @47
    @75
    @50
    @63
    wceq
    @76
    @10
    cN
    fzoval
    syl
    sumeq1d
    #
    oveq1d
    3eqtr4d
    @47
    @51
    @4
    @47
    @50
    @23
    vk
    @50
    cfn
    wcel
    @47
    @10
    cN
    fzofi
    a1i
    @47
    @25
    @50
    wcel
    @25
    @1
    wcel
    #
    @66
    @47
    @50
    @1
    @25
    @47
    @67
    cM
    @20
    wcel
    @10
    @20
    wcel
    @50
    @1
    wss
    @69
    cM
    uzid
    cM
    cM
    peano2uz
    @10
    cM
    cN
    fzoss1
    4syl
    sselda
    wph
    @84
    @66
    @11
    @84
    wph
    @65
    @66
    @25
    cM
    cN
    elfzofz
    @70
    sylan2
    adantlr
    #
    syldan
    fsumcl
    #
    wph
    @4
    cc
    wcel
    @11
    wph
    cE
    cZ
    wph
    cN
    @17
    wcel
    #
    @39
    cE
    cc
    wcel
    #
    wph
    @21
    @87
    fsumparts.1
    cM
    cN
    eluzfz2
    syl
    #
    @41
    @38
    @88
    vk
    cN
    @17
    @28
    cA
    cE
    cc
    @28
    @29
    @30
    fsumparts.e
    simpld
    eleq1d
    rspcv
    sylc
    wph
    @87
    @43
    cZ
    cc
    wcel
    #
    @89
    @45
    @42
    @90
    vk
    cN
    @17
    @28
    cV
    cZ
    cc
    @28
    @29
    @30
    fsumparts.e
    simprd
    eleq1d
    rspcv
    sylc
    mulcld
    adantr
    #
    addcomd
    eqtrd
    oveq1d
    wph
    @8
    @57
    wceq
    @11
    wph
    @8
    @1
    @55
    @48
    cmin
    co
    #
    vj
    csu
    @57
    wph
    @1
    @7
    @92
    vj
    wph
    @78
    @1
    wcel
    #
    wa
    #
    cC
    cB
    cX
    wph
    @39
    @79
    @17
    wcel
    #
    cC
    cc
    wcel
    #
    @93
    @41
    cM
    cN
    @78
    fzofzp1
    #
    @38
    @96
    vk
    @79
    @17
    @80
    cA
    cC
    cc
    @80
    @81
    @82
    fsumparts.c
    simpld
    eleq1d
    rspccva
    syl2an
    #
    wph
    @39
    @78
    @17
    wcel
    #
    cB
    cc
    wcel
    #
    @93
    @41
    @78
    cM
    cN
    elfzofz
    #
    @38
    @100
    vk
    @78
    @17
    @25
    @78
    wceq
    #
    cA
    cB
    cc
    @102
    cA
    cB
    wceq
    #
    cV
    cW
    wceq
    #
    fsumparts.b
    simpld
    eleq1d
    rspccva
    syl2an
    #
    wph
    @43
    @95
    cX
    cc
    wcel
    #
    @93
    @45
    @97
    @42
    @106
    vk
    @79
    @17
    @80
    cV
    cX
    cc
    @80
    @81
    @82
    fsumparts.c
    simprd
    eleq1d
    rspccva
    syl2an
    #
    subdird
    sumeq2dv
    wph
    @1
    @55
    @48
    vj
    @1
    cfn
    wcel
    wph
    cM
    cN
    fzofi
    a1i
    #
    @94
    cC
    cX
    @98
    @107
    mulcld
    @94
    cB
    cX
    @105
    @107
    mulcld
    #
    fsumsub
    eqtrd
    adantr
    @47
    @4
    @49
    @51
    @91
    wph
    @49
    cc
    wcel
    @11
    wph
    @1
    @48
    vj
    @108
    @109
    fsumcl
    adantr
    #
    @86
    subsub3d
    3eqtr4d
    oveq2d
    @47
    @4
    @5
    @52
    @91
    wph
    @5
    cc
    wcel
    @11
    @46
    adantr
    #
    @47
    @49
    @51
    @110
    @86
    subcld
    nnncan1d
    @47
    @49
    @51
    @5
    caddc
    co
    #
    cmin
    co
    @49
    @1
    cB
    cW
    cmul
    co
    #
    vj
    csu
    #
    cmin
    co
    #
    @54
    @3
    @47
    @112
    @114
    @49
    cmin
    @47
    @112
    @1
    @23
    vk
    csu
    #
    @114
    @47
    @112
    @5
    @51
    caddc
    co
    #
    @116
    @47
    @51
    @5
    @86
    @111
    addcomd
    @47
    @74
    @23
    vk
    csu
    @5
    @64
    caddc
    co
    @116
    @117
    @47
    @23
    @5
    vk
    cM
    @62
    wph
    @67
    @11
    @62
    @20
    wcel
    @68
    cM
    cN
    eluzp1m1
    sylan
    @47
    @25
    @74
    wcel
    #
    @84
    @66
    @47
    @84
    @118
    @47
    @1
    @74
    @25
    @77
    eleq2d
    biimpar
    @85
    syldan
    @37
    fsum1p
    @47
    @1
    @74
    @23
    vk
    @77
    sumeq1d
    @47
    @51
    @64
    @5
    caddc
    @83
    oveq2d
    3eqtr4d
    eqtr4d
    @1
    @23
    @113
    vk
    vj
    @102
    @103
    @104
    wa
    @23
    @113
    wceq
    fsumparts.b
    cA
    cB
    cV
    cW
    cmul
    oveq12
    syl
    cbvsumv
    syl6eq
    oveq2d
    @47
    @49
    @51
    @5
    @110
    @86
    @111
    subsub4d
    wph
    @3
    @115
    wceq
    @11
    wph
    @3
    @1
    @48
    @113
    cmin
    co
    #
    vj
    csu
    @115
    wph
    @1
    @2
    @119
    vj
    @94
    cB
    cX
    cW
    @105
    @107
    wph
    @43
    @99
    cW
    cc
    wcel
    #
    @93
    @45
    @101
    @42
    @120
    vk
    @78
    @17
    @102
    cV
    cW
    cc
    @102
    @103
    @104
    fsumparts.b
    simprd
    eleq1d
    rspccva
    syl2an
    #
    subdid
    sumeq2dv
    wph
    @1
    @48
    @113
    vj
    @108
    @109
    @94
    cB
    cW
    @105
    @121
    mulcld
    fsumsub
    eqtrd
    adantr
    3eqtr4d
    3eqtrrd
    wph
    @21
    @0
    @11
    wo
    fsumparts.1
    cM
    cN
    uzp1
    syl
    mpjaodan
end
