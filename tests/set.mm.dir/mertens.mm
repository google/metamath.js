include "cn0.mm"
include "csu.mm"
include "cmul.mm"
include "co.mm"
include "caddc.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cc0.mm"
include "cseq.mm"
include "cvv.mm"
include "nn0uz.mm"
include "0zd.mm"
include "wcel.mm"
include "seqex.mm"
include "a1i.mm"
include "cc.mm"
include "wa.mm"
include "cfz.mm"
include "cmin.mm"
include "fzfid.mm"
include "simpl.mm"
include "elfznn0.mm"
include "syl2an.mm"
include "wral.mm"
include "fznn0sub.mm"
include "adantl.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "weq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "sylib.mm"
include "ad2antrr.mm"
include "wceq.mm"
include "rspcv.mm"
include "sylc.mm"
include "mulcld.mm"
include "fsumcl.mm"
include "serf.mm"
include "ffvelrnda.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wrex.mm"
include "crp.mm"
include "c1.mm"
include "cn.mm"
include "c2.mm"
include "cdiv.mm"
include "cab.mm"
include "adantlr.mm"
include "cli.mm"
include "cdm.mm"
include "adantr.mm"
include "simpr.mm"
include "cbvsumv.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "sumeq1d.mm"
include "syl5eq.mm"
include "eqeq2d.mm"
include "cbvrexv.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "cbvabv.mm"
include "oveq1i.mm"
include "oveq2i.mm"
include "breq2i.mm"
include "breq1d.mm"
include "anbi2i.mm"
include "mertenslem2.mm"
include "wb.mm"
include "eluznn0.mm"
include "simpll.mm"
include "isumcl.mm"
include "syl2anc.mm"
include "simplll.mm"
include "ad2antlr.mm"
include "fsumsub.mm"
include "subdid.mm"
include "eqid.mm"
include "peano2nn0.mm"
include "syl.mm"
include "sylan.mm"
include "isumsplit.mm"
include "nn0cnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "sumeq2dv.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "nn0zd.mm"
include "iserex.mm"
include "mpbid.mm"
include "pncan2d.mm"
include "mulcomd.mm"
include "fsummulc2.mm"
include "oveq12d.mm"
include "3eqtr3rd.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl6eleq.mm"
include "fsumser.mm"
include "anasss.mm"
include "fsum0diag2.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "mpbird.mm"
include "abscvgcvg.mm"
include "isumclim2.mm"
include "rspccva.mm"
include "isermulc2.mm"
include "breqtrd.mm"
include "2clim.mm"

theorem mertens
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vi: setvar i
  let vl: setvar l
  let vu: setvar u
  let cE: class E
  let wps: wff ps
  let vw: setvar w
  let cT: class T
  assume mertens.1: |- ( ( ph /\ j e. NN0 ) -> ( F ` j ) = A )
  assume mertens.2: |- ( ( ph /\ j e. NN0 ) -> ( K ` j ) = ( abs ` A ) )
  assume mertens.3: |- ( ( ph /\ j e. NN0 ) -> A e. CC )
  assume mertens.4: |- ( ( ph /\ k e. NN0 ) -> ( G ` k ) = B )
  assume mertens.5: |- ( ( ph /\ k e. NN0 ) -> B e. CC )
  assume mertens.6: |- ( ( ph /\ k e. NN0 ) -> ( H ` k ) = sum_ j e. ( 0 ... k ) ( A x. ( G ` ( k - j ) ) ) )
  assume mertens.7: |- ( ph -> seq 0 ( + , K ) e. dom ~~> )
  assume mertens.8: |- ( ph -> seq 0 ( + , G ) e. dom ~~> )

  disjoint B j
  disjoint j k
  disjoint G j
  disjoint G k
  disjoint j ph
  disjoint k ph
  disjoint A k
  disjoint K j
  disjoint K k
  disjoint F j
  disjoint H k
  disjoint j m
  disjoint j n
  disjoint j s
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint m n
  disjoint m s
  disjoint m t
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint n s
  disjoint n t
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint s t
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint B s
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i m
  disjoint i n
  disjoint i s
  disjoint i u
  disjoint i y
  disjoint i z
  disjoint G i
  disjoint j l
  disjoint j u
  disjoint k l
  disjoint k m
  disjoint k n
  disjoint k s
  disjoint k u
  disjoint k y
  disjoint k z
  disjoint l m
  disjoint l n
  disjoint l s
  disjoint l u
  disjoint l y
  disjoint l z
  disjoint G l
  disjoint m u
  disjoint G m
  disjoint n u
  disjoint G n
  disjoint s u
  disjoint G s
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint G y
  disjoint G z
  disjoint k x
  disjoint m ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint k t
  disjoint A m
  disjoint A n
  disjoint A s
  disjoint A t
  disjoint A y
  disjoint E j
  disjoint E k
  disjoint E m
  disjoint E n
  disjoint E s
  disjoint E t
  disjoint E y
  disjoint E z
  disjoint i t
  disjoint K i
  disjoint K m
  disjoint K n
  disjoint K s
  disjoint t u
  disjoint K t
  disjoint K u
  disjoint K y
  disjoint K z
  disjoint F m
  disjoint F n
  disjoint u x
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint j ps
  disjoint k ps
  disjoint m ps
  disjoint n ps
  disjoint ps t
  disjoint ps y
  disjoint ps z
  disjoint j w
  disjoint T j
  disjoint k w
  disjoint T k
  disjoint m w
  disjoint T m
  disjoint n w
  disjoint T n
  disjoint t w
  disjoint T t
  disjoint w y
  disjoint w z
  disjoint T w
  disjoint T y
  disjoint T z
  disjoint H m
  disjoint H x
  disjoint H y
  disjoint n ph
  disjoint ph s
  assert |- ( ph -> seq 0 ( + , H ) ~~> ( sum_ j e. NN0 A x. sum_ k e. NN0 B ) )

  proof
    wph
    vx
    cn0
    cA
    vj
    csu
    #
    cn0
    cB
    vk
    csu
    #
    cmul
    co
    #
    vy
    vm
    caddc
    vn
    cn0
    @1
    vn
    cv
    #
    cF
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cc0
    cseq
    #
    caddc
    cH
    cc0
    cseq
    #
    cc0
    cvv
    cn0
    nn0uz
    wph
    0zd
    #
    @8
    cvv
    wcel
    wph
    caddc
    cH
    cc0
    seqex
    a1i
    wph
    cn0
    cc
    vm
    cv
    #
    @8
    wph
    vk
    cH
    cc0
    cn0
    nn0uz
    @9
    wph
    vk
    cv
    #
    cn0
    wcel
    #
    wa
    #
    @11
    cH
    cfv
    #
    cc0
    @11
    cfz
    co
    #
    cA
    @11
    vj
    cv
    #
    cmin
    co
    #
    cG
    cfv
    #
    cmul
    co
    #
    vj
    csu
    #
    cc
    mertens.6
    @13
    @15
    @19
    vj
    @13
    cc0
    @11
    fzfid
    @13
    @16
    @15
    wcel
    #
    wa
    #
    cA
    @18
    @13
    wph
    @16
    cn0
    wcel
    #
    cA
    cc
    wcel
    #
    @21
    wph
    @12
    simpl
    @16
    @11
    elfznn0
    mertens.3
    syl2an
    @22
    @17
    cn0
    wcel
    #
    vi
    cv
    #
    cG
    cfv
    #
    cc
    wcel
    #
    vi
    cn0
    wral
    #
    @18
    cc
    wcel
    #
    @21
    @25
    @13
    @16
    cc0
    @11
    fznn0sub
    adantl
    wph
    @29
    @12
    @21
    wph
    @11
    cG
    cfv
    #
    cc
    wcel
    #
    vk
    cn0
    wral
    @29
    wph
    @32
    vk
    cn0
    @13
    @31
    cB
    cc
    mertens.4
    mertens.5
    eqeltrd
    #
    ralrimiva
    @32
    @28
    vk
    vi
    cn0
    vk
    vi
    weq
    @31
    @27
    cc
    @11
    @26
    cG
    fveq2
    eleq1d
    cbvralv
    sylib
    ad2antrr
    @28
    @30
    vi
    @17
    cn0
    @26
    @17
    wceq
    @27
    @18
    cc
    @26
    @17
    cG
    fveq2
    eleq1d
    rspcv
    sylc
    mulcld
    fsumcl
    #
    eqeltrd
    serf
    ffvelrnda
    wph
    @10
    @7
    cfv
    #
    @10
    @8
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
    vm
    vy
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vy
    cn0
    wrex
    #
    vx
    crp
    wph
    @39
    crp
    wcel
    #
    wa
    #
    @44
    cc0
    @10
    cfz
    co
    #
    cA
    @10
    @16
    cmin
    co
    #
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    cB
    vk
    csu
    #
    cmul
    co
    #
    vj
    csu
    #
    cabs
    cfv
    #
    @39
    clt
    wbr
    #
    vm
    @42
    wral
    #
    vy
    cn0
    wrex
    #
    @46
    vs
    cv
    #
    cn
    wcel
    #
    vu
    cv
    #
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @27
    vi
    csu
    #
    cabs
    cfv
    #
    @39
    c2
    cdiv
    co
    #
    cn0
    @26
    cK
    cfv
    #
    vi
    csu
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    clt
    wbr
    #
    vu
    @58
    cuz
    cfv
    #
    wral
    #
    wa
    vy
    vz
    cA
    cB
    @60
    @26
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    vl
    cv
    #
    cG
    cfv
    #
    vl
    csu
    #
    cabs
    cfv
    #
    wceq
    #
    vi
    cc0
    @58
    c1
    cmin
    co
    cfz
    co
    #
    wrex
    #
    vu
    cab
    vj
    vk
    vm
    vn
    @39
    cF
    cG
    cH
    cK
    vs
    wph
    @23
    @16
    cF
    cfv
    #
    cA
    wceq
    @45
    mertens.1
    adantlr
    wph
    @23
    @16
    cK
    cfv
    #
    cA
    cabs
    cfv
    #
    wceq
    @45
    mertens.2
    adantlr
    wph
    @23
    @24
    @45
    mertens.3
    adantlr
    wph
    @12
    @31
    cB
    wceq
    #
    @45
    mertens.4
    adantlr
    wph
    @12
    cB
    cc
    wcel
    #
    @45
    mertens.5
    adantlr
    wph
    @12
    @14
    @20
    wceq
    #
    @45
    mertens.6
    adantlr
    wph
    caddc
    cK
    cc0
    cseq
    cli
    cdm
    #
    wcel
    @45
    mertens.7
    adantr
    wph
    caddc
    cG
    cc0
    cseq
    @88
    wcel
    #
    @45
    mertens.8
    adantr
    wph
    @45
    simpr
    @81
    vz
    cv
    #
    @3
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    @31
    vk
    csu
    #
    cabs
    cfv
    #
    wceq
    #
    vn
    @80
    wrex
    #
    vu
    vz
    @81
    @60
    @94
    wceq
    #
    vn
    @80
    wrex
    vu
    vz
    weq
    #
    @96
    @79
    @97
    vi
    vn
    @80
    vi
    vn
    weq
    #
    @78
    @94
    @60
    @99
    @77
    @93
    cabs
    @99
    @77
    @74
    @31
    vk
    csu
    @93
    @74
    @76
    @31
    vl
    vk
    @75
    @11
    cG
    fveq2
    cbvsumv
    @99
    @74
    @92
    @31
    vk
    @99
    @73
    @91
    cuz
    @26
    @3
    c1
    caddc
    oveq1
    fveq2d
    sumeq1d
    syl5eq
    fveq2d
    eqeq2d
    cbvrexv
    @98
    @97
    @95
    vn
    @80
    @60
    @90
    @94
    eqeq1
    rexbidv
    syl5bb
    cbvabv
    @72
    @94
    @65
    cn0
    @83
    vj
    csu
    #
    c1
    caddc
    co
    #
    cdiv
    co
    #
    clt
    wbr
    #
    vn
    @71
    wral
    @59
    @70
    @103
    vu
    vn
    @71
    @70
    @64
    @102
    clt
    wbr
    vu
    vn
    weq
    #
    @103
    @69
    @102
    @64
    clt
    @68
    @101
    @65
    cdiv
    @67
    @100
    c1
    caddc
    cn0
    @66
    @83
    vi
    vj
    @26
    @16
    cK
    fveq2
    cbvsumv
    oveq1i
    oveq2i
    breq2i
    @104
    @64
    @94
    @102
    clt
    @104
    @63
    @93
    cabs
    @104
    @63
    @62
    @31
    vk
    csu
    @93
    @62
    @27
    @31
    vi
    vk
    @26
    @11
    cG
    fveq2
    cbvsumv
    @104
    @62
    @92
    @31
    vk
    @104
    @61
    @91
    cuz
    @60
    @3
    c1
    caddc
    oveq1
    fveq2d
    sumeq1d
    syl5eq
    fveq2d
    breq1d
    syl5bb
    cbvralv
    anbi2i
    mertenslem2
    wph
    @44
    @57
    wb
    @45
    wph
    @43
    @56
    vy
    cn0
    wph
    @41
    cn0
    wcel
    #
    wa
    @40
    @55
    vm
    @42
    wph
    @105
    @10
    @42
    wcel
    #
    @40
    @55
    wb
    #
    @105
    @106
    wa
    wph
    @10
    cn0
    wcel
    #
    @107
    @10
    @41
    eluznn0
    wph
    @108
    wa
    #
    @38
    @54
    @39
    clt
    @109
    @37
    @53
    cabs
    @109
    @47
    @1
    @82
    cmul
    co
    #
    cc0
    @48
    cfz
    co
    #
    cA
    @31
    cmul
    co
    #
    vk
    csu
    #
    cmin
    co
    #
    vj
    csu
    @47
    @110
    vj
    csu
    #
    @47
    @113
    vj
    csu
    #
    cmin
    co
    @53
    @37
    @109
    @47
    @110
    @113
    vj
    @109
    cc0
    @10
    fzfid
    @109
    @16
    @47
    wcel
    #
    wa
    #
    wph
    @23
    @110
    cc
    wcel
    wph
    @108
    @117
    simpll
    #
    @117
    @23
    @109
    @16
    @10
    elfznn0
    #
    adantl
    #
    wph
    @23
    wa
    #
    @1
    @82
    wph
    @1
    cc
    wcel
    #
    @23
    wph
    cB
    vk
    cG
    cc0
    cn0
    nn0uz
    @9
    mertens.4
    mertens.5
    mertens.8
    isumcl
    #
    adantr
    #
    @122
    @82
    cA
    cc
    mertens.1
    mertens.3
    eqeltrd
    #
    mulcld
    syl2anc
    #
    @118
    @111
    @112
    vk
    @118
    cc0
    @48
    fzfid
    #
    @118
    @11
    @111
    wcel
    #
    wa
    #
    cA
    @31
    @130
    wph
    @23
    @24
    wph
    @108
    @117
    @129
    simplll
    #
    @117
    @23
    @109
    @129
    @120
    ad2antlr
    mertens.3
    syl2anc
    @130
    wph
    @12
    @32
    @131
    @129
    @12
    @118
    @11
    @48
    elfznn0
    adantl
    #
    @33
    syl2anc
    #
    mulcld
    #
    fsumcl
    fsumsub
    @109
    @47
    @114
    @52
    vj
    @118
    cA
    @1
    @111
    @31
    vk
    csu
    #
    cmin
    co
    #
    cmul
    co
    cA
    @1
    cmul
    co
    #
    cA
    @135
    cmul
    co
    #
    cmin
    co
    @52
    @114
    @118
    cA
    @1
    @135
    @118
    wph
    @23
    @24
    @119
    @121
    mertens.3
    syl2anc
    #
    wph
    @123
    @108
    @117
    @124
    ad2antrr
    @118
    @111
    @31
    vk
    @128
    @133
    fsumcl
    #
    subdid
    @118
    @136
    @51
    cA
    cmul
    @118
    @136
    @135
    @51
    caddc
    co
    #
    @135
    cmin
    co
    @51
    @118
    @1
    @141
    @135
    cmin
    @118
    @1
    cc0
    @49
    c1
    cmin
    co
    #
    cfz
    co
    #
    cB
    vk
    csu
    #
    @51
    caddc
    co
    @141
    @118
    cB
    vk
    cG
    cc0
    @49
    @50
    cn0
    nn0uz
    @50
    eqid
    #
    @118
    @48
    cn0
    wcel
    #
    @49
    cn0
    wcel
    #
    @117
    @146
    @109
    @16
    cc0
    @10
    fznn0sub
    adantl
    #
    @48
    peano2nn0
    syl
    #
    @118
    wph
    @12
    @85
    @119
    mertens.4
    sylan
    #
    @118
    wph
    @12
    @86
    @119
    mertens.5
    sylan
    #
    wph
    @89
    @108
    @117
    mertens.8
    ad2antrr
    #
    isumsplit
    @118
    @144
    @135
    @51
    caddc
    @118
    @144
    @111
    cB
    vk
    csu
    @135
    @118
    @143
    @111
    cB
    vk
    @118
    @142
    @48
    cc0
    cfz
    @118
    @48
    cc
    wcel
    c1
    cc
    wcel
    @142
    @48
    wceq
    @118
    @48
    @148
    nn0cnd
    ax-1cn
    @48
    c1
    pncan
    sylancl
    oveq2d
    sumeq1d
    @118
    @111
    @31
    cB
    vk
    @130
    wph
    @12
    @85
    @131
    @132
    mertens.4
    syl2anc
    sumeq2dv
    eqtr4d
    oveq1d
    eqtrd
    oveq1d
    @118
    @135
    @51
    @140
    @118
    cB
    vk
    cG
    @49
    @50
    @145
    @118
    @49
    @149
    nn0zd
    @118
    @11
    @50
    wcel
    #
    wa
    #
    wph
    @12
    @85
    wph
    @108
    @117
    @153
    simplll
    #
    @118
    @147
    @153
    @12
    @149
    @11
    @49
    eluznn0
    sylan
    #
    mertens.4
    syl2anc
    @154
    wph
    @12
    @86
    @155
    @156
    mertens.5
    syl2anc
    @118
    @89
    caddc
    cG
    @49
    cseq
    @88
    wcel
    @152
    @118
    vk
    cG
    cc0
    @49
    cn0
    nn0uz
    @149
    @118
    @12
    wa
    @31
    cB
    cc
    @150
    @151
    eqeltrd
    iserex
    mpbid
    isumcl
    pncan2d
    eqtrd
    oveq2d
    @118
    @137
    @110
    @138
    @113
    cmin
    @118
    wph
    @23
    @137
    @110
    wceq
    @119
    @121
    @122
    @137
    @1
    cA
    cmul
    co
    @110
    @122
    cA
    @1
    mertens.3
    @125
    mulcomd
    @122
    @82
    cA
    @1
    cmul
    mertens.1
    oveq2d
    eqtr4d
    syl2anc
    @118
    @111
    @31
    cA
    vk
    @128
    @139
    @133
    fsummulc2
    oveq12d
    3eqtr3rd
    sumeq2dv
    @109
    @115
    @35
    @116
    @36
    cmin
    @109
    @110
    vj
    @6
    cc0
    @10
    @118
    @23
    @16
    @6
    cfv
    @110
    wceq
    @121
    vn
    @16
    @5
    @110
    cn0
    @6
    vn
    vj
    weq
    @4
    @82
    @1
    cmul
    @3
    @16
    cF
    fveq2
    oveq2d
    @6
    eqid
    #
    @1
    @82
    cmul
    ovex
    fvmpt
    syl
    @109
    @10
    cn0
    cc0
    cuz
    cfv
    wph
    @108
    simpr
    nn0uz
    syl6eleq
    #
    @127
    fsumser
    @109
    @116
    @47
    @20
    vk
    csu
    @36
    @109
    vn
    @112
    cA
    @3
    cG
    cfv
    #
    cmul
    co
    @19
    vj
    vk
    @10
    vn
    vk
    weq
    @159
    @31
    cA
    cmul
    @3
    @11
    cG
    fveq2
    oveq2d
    @3
    @17
    wceq
    @159
    @18
    cA
    cmul
    @3
    @17
    cG
    fveq2
    oveq2d
    @109
    @117
    @129
    @112
    cc
    wcel
    @134
    anasss
    fsum0diag2
    @109
    @20
    vk
    cH
    cc0
    @10
    @109
    @11
    @47
    wcel
    #
    wa
    #
    wph
    @12
    @87
    wph
    @108
    @160
    simpll
    #
    @160
    @12
    @109
    @11
    @10
    elfznn0
    adantl
    #
    mertens.6
    syl2anc
    @158
    @161
    wph
    @12
    @20
    cc
    wcel
    @162
    @163
    @34
    syl2anc
    fsumser
    eqtrd
    oveq12d
    3eqtr3rd
    fveq2d
    breq1d
    sylan2
    anassrs
    ralbidva
    rexbidva
    adantr
    mpbird
    ralrimiva
    wph
    @7
    @1
    @0
    cmul
    co
    @2
    cli
    wph
    @0
    @1
    vm
    cF
    @6
    cc0
    cn0
    nn0uz
    @9
    @124
    wph
    cA
    vj
    cF
    cc0
    cn0
    nn0uz
    @9
    mertens.1
    mertens.3
    wph
    vj
    cK
    cF
    cc0
    cn0
    nn0uz
    @9
    @122
    @83
    @84
    @82
    cabs
    cfv
    mertens.2
    @122
    @82
    cA
    cabs
    mertens.1
    fveq2d
    eqtr4d
    @126
    mertens.7
    abscvgcvg
    #
    isumclim2
    wph
    @82
    cc
    wcel
    #
    vj
    cn0
    wral
    @108
    @10
    cF
    cfv
    #
    cc
    wcel
    #
    wph
    @165
    vj
    cn0
    @126
    ralrimiva
    @165
    @167
    vj
    @10
    cn0
    vj
    vm
    weq
    @82
    @166
    cc
    @16
    @10
    cF
    fveq2
    eleq1d
    rspccva
    sylan
    @108
    @10
    @6
    cfv
    @1
    @166
    cmul
    co
    #
    wceq
    wph
    vn
    @10
    @5
    @168
    cn0
    @6
    vn
    vm
    weq
    @4
    @166
    @1
    cmul
    @3
    @10
    cF
    fveq2
    oveq2d
    @157
    @1
    @166
    cmul
    ovex
    fvmpt
    adantl
    isermulc2
    wph
    @1
    @0
    @124
    wph
    cA
    vj
    cF
    cc0
    cn0
    nn0uz
    @9
    mertens.1
    mertens.3
    @164
    isumcl
    mulcomd
    breqtrd
    2clim
end
