include "cv.mm"
include "c4.mm"
include "c3.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cmul.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cle.mm"
include "wa.mm"
include "caddc.mm"
include "cr.mm"
include "wrex.mm"
include "wral.mm"
include "wex.mm"
include "cn.mm"
include "wcel.mm"
include "cc0.mm"
include "cfz.mm"
include "wf.mm"
include "w3a.mm"
include "nnre.mm"
include "adantl.mm"
include "rpred.mm"
include "adantr.mm"
include "wne.mm"
include "rpne0d.mm"
include "redivcld.mm"
include "1red.mm"
include "readdcld.mm"
include "arch.mm"
include "syl.mm"
include "nfv.mm"
include "nfan.mm"
include "nfra1.mm"
include "simp-5l.mm"
include "fcnre.mm"
include "ffvelrnda.mm"
include "sylancom.mm"
include "simp-5r.mm"
include "nnred.mm"
include "simpllr.mm"
include "resubcld.mm"
include "remulcld.mm"
include "r19.21bi.mm"
include "simplr.mm"
include "simpr.mm"
include "simpl1.mm"
include "simpl2.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "ltaddsubd.mm"
include "mpbid.mm"
include "wb.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "rpgt0d.mm"
include "ltdivmul2.mm"
include "syl112anc.mm"
include "syl31anc.mm"
include "lttrd.mm"
include "ex.mm"
include "ralrimi.mm"
include "reximdva.mm"
include "mpd.mm"
include "rfcnnnub.mm"
include "r19.29a.mm"
include "df-rex.mm"
include "sylib.mm"
include "crab.mm"
include "cmpt.mm"
include "eqid.mm"
include "ccmp.mm"
include "wss.mm"
include "3adant1r.mm"
include "adantlr.mm"
include "crp.mm"
include "stoweidlem59.mm"
include "adantrr.mm"
include "19.42v.mm"
include "sylanbrc.mm"
include "3anass.mm"
include "exbii.mm"
include "sylibr.mm"
include "eximdv.mm"
include "csu.mm"
include "simpl.mm"
include "simpr1l.mm"
include "simpr2.mm"
include "nf3an.mm"
include "simp2.mm"
include "simp3.mm"
include "simp1.mm"
include "syl3an1.mm"
include "3ad2antl1.mm"
include "sselda.mm"
include "stoweidlem17.mm"
include "syl3anc.mm"
include "nfcv.mm"
include "nfral.mm"
include "cvv.mm"
include "cuni.mm"
include "uniexg.mm"
include "syl5eqel.mm"
include "simpr1r.mm"
include "simpll.mm"
include "simplr2.mm"
include "ffvelrn.mm"
include "3adant1.mm"
include "simp1r3.mm"
include "r19.26-3.mm"
include "simp1bi.mm"
include "2ralimi.mm"
include "3syl.mm"
include "rspa.mm"
include "syl21anc.mm"
include "simp2bi.mm"
include "simp3bi.mm"
include "stoweidlem34.mm"
include "wceq.mm"
include "nfmpt1.mm"
include "nfeq2.mm"
include "fveq1.mm"
include "breq1d.mm"
include "breq2d.mm"
include "anbi12d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "ralbid.mm"
include "rspcev.mm"
include "2eximdv.mm"
include "idd.mm"
include "exlimdv.mm"

theorem stoweidlem60
  let wph: wff ph
  let vy: setvar y
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cJ: class J
  let cK: class K
  let vr: setvar r
  let vq: setvar q
  let vi: setvar i
  let vx: setvar x
  let vm: setvar m
  let vk: setvar k
  assume stoweidlem60.1: |- F/_ t F
  assume stoweidlem60.2: |- F/ t ph
  assume stoweidlem60.3: |- K = ( topGen ` ran (,) )
  assume stoweidlem60.4: |- T = U. J
  assume stoweidlem60.5: |- C = ( J Cn K )
  assume stoweidlem60.6: |- D = ( j e. ( 0 ... n ) |-> { t e. T | ( F ` t ) <_ ( ( j - ( 1 / 3 ) ) x. E ) } )
  assume stoweidlem60.7: |- B = ( j e. ( 0 ... n ) |-> { t e. T | ( ( j + ( 1 / 3 ) ) x. E ) <_ ( F ` t ) } )
  assume stoweidlem60.8: |- ( ph -> J e. Comp )
  assume stoweidlem60.9: |- ( ph -> T =/= (/) )
  assume stoweidlem60.10: |- ( ph -> A C_ C )
  assume stoweidlem60.11: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) + ( g ` t ) ) ) e. A )
  assume stoweidlem60.12: |- ( ( ph /\ f e. A /\ g e. A ) -> ( t e. T |-> ( ( f ` t ) x. ( g ` t ) ) ) e. A )
  assume stoweidlem60.13: |- ( ( ph /\ y e. RR ) -> ( t e. T |-> y ) e. A )
  assume stoweidlem60.14: |- ( ( ph /\ ( r e. T /\ t e. T /\ r =/= t ) ) -> E. q e. A ( q ` r ) =/= ( q ` t ) )
  assume stoweidlem60.15: |- ( ph -> F e. C )
  assume stoweidlem60.16: |- ( ph -> A. t e. T 0 <_ ( F ` t ) )
  assume stoweidlem60.17: |- ( ph -> E e. RR+ )
  assume stoweidlem60.18: |- ( ph -> E < ( 1 / 3 ) )

  disjoint f g
  disjoint f j
  disjoint f n
  disjoint f t
  disjoint A f
  disjoint g j
  disjoint g n
  disjoint g t
  disjoint A g
  disjoint j n
  disjoint j t
  disjoint A j
  disjoint n t
  disjoint A n
  disjoint A t
  disjoint f q
  disjoint f r
  disjoint g q
  disjoint g r
  disjoint j q
  disjoint j r
  disjoint n q
  disjoint n r
  disjoint q r
  disjoint q t
  disjoint A q
  disjoint r t
  disjoint A r
  disjoint f y
  disjoint j y
  disjoint n y
  disjoint q y
  disjoint r y
  disjoint t y
  disjoint A y
  disjoint B f
  disjoint B g
  disjoint D f
  disjoint D g
  disjoint E f
  disjoint E g
  disjoint E j
  disjoint E n
  disjoint E t
  disjoint J f
  disjoint J g
  disjoint J r
  disjoint J t
  disjoint T f
  disjoint T g
  disjoint T j
  disjoint T n
  disjoint T t
  disjoint f ph
  disjoint g ph
  disjoint j ph
  disjoint n ph
  disjoint F g
  disjoint F j
  disjoint F n
  disjoint B q
  disjoint B r
  disjoint B y
  disjoint D q
  disjoint D r
  disjoint D y
  disjoint T q
  disjoint T r
  disjoint T y
  disjoint ph q
  disjoint ph r
  disjoint ph y
  disjoint E r
  disjoint E y
  disjoint K t
  disjoint f i
  disjoint f x
  disjoint g i
  disjoint g x
  disjoint i j
  disjoint i n
  disjoint i t
  disjoint i x
  disjoint A i
  disjoint j x
  disjoint n x
  disjoint t x
  disjoint A x
  disjoint B i
  disjoint B x
  disjoint D i
  disjoint D x
  disjoint E i
  disjoint E x
  disjoint T i
  disjoint T x
  disjoint i ph
  disjoint ph x
  disjoint F i
  disjoint F x
  disjoint m n
  disjoint m t
  disjoint E m
  disjoint F m
  disjoint T m
  disjoint m ph
  disjoint x y
  disjoint k x
  assert |- ( ph -> E. g e. A A. t e. T E. j e. RR ( ( ( ( j - ( 4 / 3 ) ) x. E ) < ( F ` t ) /\ ( F ` t ) <_ ( ( j - ( 1 / 3 ) ) x. E ) ) /\ ( ( g ` t ) < ( ( j + ( 1 / 3 ) ) x. E ) /\ ( ( j - ( 4 / 3 ) ) x. E ) < ( g ` t ) ) ) )

  proof
    wph
    vj
    cv
    #
    c4
    c3
    cdiv
    co
    cmin
    co
    cE
    cmul
    co
    #
    vt
    cv
    #
    cF
    cfv
    #
    clt
    wbr
    @3
    @0
    c1
    c3
    cdiv
    co
    #
    cmin
    co
    cE
    cmul
    co
    cle
    wbr
    wa
    #
    @2
    vg
    cv
    #
    cfv
    #
    @0
    @4
    caddc
    co
    cE
    cmul
    co
    #
    clt
    wbr
    #
    @1
    @7
    clt
    wbr
    #
    wa
    #
    wa
    #
    vj
    cr
    wrex
    #
    vt
    cT
    wral
    #
    vg
    cA
    wrex
    #
    vx
    wex
    #
    @15
    wph
    @16
    vn
    wex
    #
    @16
    wph
    vn
    cv
    #
    cn
    wcel
    #
    @3
    @18
    c1
    cmin
    co
    #
    cE
    cmul
    co
    #
    clt
    wbr
    #
    vt
    cT
    wral
    #
    wa
    #
    cc0
    @18
    cfz
    co
    #
    cA
    vx
    cv
    #
    wf
    #
    cc0
    @2
    @0
    @26
    cfv
    #
    cfv
    #
    cle
    wbr
    #
    @29
    c1
    cle
    wbr
    #
    wa
    #
    vt
    cT
    wral
    #
    @29
    cE
    @18
    cdiv
    co
    #
    clt
    wbr
    #
    vt
    @0
    cD
    cfv
    #
    wral
    #
    c1
    @34
    cmin
    co
    #
    @29
    clt
    wbr
    #
    vt
    @0
    cB
    cfv
    #
    wral
    #
    w3a
    #
    vj
    @25
    wral
    #
    w3a
    #
    vx
    wex
    #
    vn
    wex
    #
    @17
    wph
    @24
    vn
    wex
    #
    @46
    wph
    @23
    vn
    cn
    wrex
    #
    @47
    wph
    @3
    vm
    cv
    #
    clt
    wbr
    #
    vt
    cT
    wral
    #
    @48
    vm
    cn
    wph
    @49
    cn
    wcel
    #
    wa
    #
    @51
    wa
    #
    @49
    cE
    cdiv
    co
    #
    c1
    caddc
    co
    #
    @18
    clt
    wbr
    #
    vn
    cn
    wrex
    #
    @48
    @54
    @56
    cr
    wcel
    #
    @58
    @53
    @59
    @51
    @53
    @55
    c1
    @53
    @49
    cE
    @52
    @49
    cr
    wcel
    #
    wph
    @49
    nnre
    #
    adantl
    wph
    cE
    cr
    wcel
    #
    @52
    wph
    cE
    stoweidlem60.17
    rpred
    #
    adantr
    wph
    cE
    cc0
    wne
    @52
    wph
    cE
    stoweidlem60.17
    rpne0d
    adantr
    redivcld
    #
    @53
    1red
    readdcld
    adantr
    @56
    vn
    arch
    syl
    @54
    @57
    @23
    vn
    cn
    @54
    @19
    wa
    #
    @57
    @23
    @65
    @57
    wa
    #
    @22
    vt
    cT
    @65
    @57
    vt
    @54
    @19
    vt
    @53
    @51
    vt
    wph
    @52
    vt
    stoweidlem60.2
    @52
    vt
    nfv
    nfan
    @50
    vt
    cT
    nfra1
    nfan
    @19
    vt
    nfv
    #
    nfan
    @57
    vt
    nfv
    nfan
    @66
    @2
    cT
    wcel
    #
    @22
    @66
    @68
    wa
    #
    @3
    @49
    @21
    @66
    @68
    wph
    @3
    cr
    wcel
    wph
    @52
    @51
    @19
    @57
    @68
    simp-5l
    #
    wph
    cT
    cr
    @2
    cF
    wph
    cC
    cT
    cF
    cJ
    cK
    stoweidlem60.3
    stoweidlem60.4
    stoweidlem60.5
    stoweidlem60.15
    fcnre
    #
    ffvelrnda
    sylancom
    @69
    @49
    wph
    @52
    @51
    @19
    @57
    @68
    simp-5r
    #
    nnred
    @69
    @20
    cE
    @69
    @18
    c1
    @69
    @18
    @54
    @19
    @57
    @68
    simpllr
    #
    nnred
    @69
    1red
    resubcld
    @69
    wph
    @62
    @70
    @63
    syl
    remulcld
    @66
    @50
    vt
    cT
    @53
    @51
    @19
    @57
    simpllr
    r19.21bi
    @69
    wph
    @52
    @19
    @57
    @49
    @21
    clt
    wbr
    #
    @70
    @72
    @73
    @65
    @57
    @68
    simplr
    wph
    @52
    @19
    w3a
    #
    @57
    wa
    #
    @55
    @20
    clt
    wbr
    #
    @74
    @76
    @57
    @77
    @75
    @57
    simpr
    @76
    @55
    c1
    @18
    @76
    wph
    @52
    @55
    cr
    wcel
    wph
    @52
    @19
    @57
    simpl1
    #
    wph
    @52
    @19
    @57
    simpl2
    @64
    syl2anc
    @76
    1red
    #
    @76
    @18
    wph
    @52
    @19
    @57
    simpl3
    nnred
    #
    ltaddsubd
    mpbid
    @76
    @60
    @20
    cr
    wcel
    @62
    cc0
    cE
    clt
    wbr
    #
    @77
    @74
    wb
    @75
    @60
    @57
    @52
    wph
    @60
    @19
    @61
    3ad2ant2
    adantr
    @76
    @18
    c1
    @80
    @79
    resubcld
    @75
    @62
    @57
    wph
    @52
    @62
    @19
    @63
    3ad2ant1
    adantr
    @76
    wph
    @81
    @78
    wph
    cE
    stoweidlem60.17
    rpgt0d
    syl
    @49
    @20
    cE
    ltdivmul2
    syl112anc
    mpbid
    syl31anc
    lttrd
    ex
    ralrimi
    ex
    reximdva
    mpd
    wph
    vt
    cC
    cT
    vm
    cF
    cJ
    cK
    stoweidlem60.1
    stoweidlem60.2
    stoweidlem60.3
    stoweidlem60.8
    stoweidlem60.4
    stoweidlem60.9
    stoweidlem60.5
    stoweidlem60.15
    rfcnnnub
    r19.29a
    @23
    vn
    cn
    df-rex
    sylib
    wph
    @24
    @45
    vn
    wph
    @24
    @45
    wph
    @24
    wa
    #
    @24
    @27
    @43
    wa
    #
    wa
    #
    vx
    wex
    #
    @45
    @82
    @24
    @83
    vx
    wex
    #
    @85
    wph
    @24
    simpr
    wph
    @19
    @86
    @23
    wph
    @19
    wa
    vx
    vy
    vt
    cA
    cB
    cC
    cD
    cT
    vf
    vg
    vj
    cE
    cF
    vj
    @25
    @2
    vy
    cv
    #
    cfv
    #
    @34
    clt
    wbr
    vt
    @36
    wral
    @38
    @88
    clt
    wbr
    vt
    @40
    wral
    wa
    vy
    cc0
    @88
    cle
    wbr
    @88
    c1
    cle
    wbr
    wa
    vt
    cT
    wral
    vy
    cA
    crab
    #
    crab
    cmpt
    #
    cJ
    cK
    @18
    @89
    vr
    vq
    stoweidlem60.1
    wph
    @19
    vt
    stoweidlem60.2
    @67
    nfan
    stoweidlem60.3
    stoweidlem60.4
    stoweidlem60.5
    stoweidlem60.6
    stoweidlem60.7
    @89
    eqid
    @90
    eqid
    wph
    cJ
    ccmp
    wcel
    #
    @19
    stoweidlem60.8
    adantr
    wph
    cA
    cC
    wss
    @19
    stoweidlem60.10
    adantr
    wph
    vf
    cv
    #
    cA
    wcel
    #
    @6
    cA
    wcel
    #
    vt
    cT
    @2
    @92
    cfv
    #
    @7
    caddc
    co
    cmpt
    cA
    wcel
    #
    @19
    stoweidlem60.11
    3adant1r
    wph
    @93
    @94
    vt
    cT
    @95
    @7
    cmul
    co
    cmpt
    cA
    wcel
    #
    @19
    stoweidlem60.12
    3adant1r
    wph
    @87
    cr
    wcel
    #
    vt
    cT
    @87
    cmpt
    cA
    wcel
    #
    @19
    stoweidlem60.13
    adantlr
    wph
    vr
    cv
    #
    cT
    wcel
    @68
    @100
    @2
    wne
    w3a
    @100
    vq
    cv
    #
    cfv
    @2
    @101
    cfv
    wne
    vq
    cA
    wrex
    @19
    stoweidlem60.14
    adantlr
    wph
    cF
    cC
    wcel
    @19
    stoweidlem60.15
    adantr
    wph
    cE
    crp
    wcel
    #
    @19
    stoweidlem60.17
    adantr
    wph
    cE
    @4
    clt
    wbr
    #
    @19
    stoweidlem60.18
    adantr
    wph
    @19
    simpr
    stoweidlem59
    adantrr
    @24
    @83
    vx
    19.42v
    sylanbrc
    @44
    @84
    vx
    @24
    @27
    @43
    3anass
    exbii
    sylibr
    ex
    eximdv
    mpd
    wph
    @44
    @15
    vn
    vx
    wph
    @44
    @15
    wph
    @44
    wa
    #
    vt
    cT
    @25
    cE
    @2
    vi
    cv
    @26
    cfv
    cfv
    cmul
    co
    vi
    csu
    #
    cmpt
    #
    cA
    wcel
    #
    @5
    @2
    @106
    cfv
    #
    @8
    clt
    wbr
    #
    @1
    @108
    clt
    wbr
    #
    wa
    #
    wa
    #
    vj
    cr
    wrex
    #
    vt
    cT
    wral
    #
    @15
    @104
    wph
    @19
    @27
    @107
    wph
    @44
    simpl
    @19
    @23
    @27
    @43
    wph
    simpr1l
    #
    wph
    @24
    @27
    @43
    simpr2
    wph
    @19
    @27
    w3a
    #
    vy
    vt
    cA
    cT
    vf
    vg
    vi
    cE
    @18
    @26
    wph
    @19
    @27
    vt
    stoweidlem60.2
    @67
    @27
    vt
    nfv
    #
    nf3an
    wph
    @19
    @27
    simp2
    wph
    @19
    @27
    simp3
    @116
    wph
    @93
    @94
    @96
    wph
    @19
    @27
    simp1
    #
    stoweidlem60.11
    syl3an1
    @116
    wph
    @93
    @94
    @97
    @118
    stoweidlem60.12
    syl3an1
    wph
    @19
    @98
    @99
    @27
    stoweidlem60.13
    3ad2antl1
    @116
    cE
    wph
    @19
    @102
    @27
    stoweidlem60.17
    3ad2ant1
    rpred
    wph
    @19
    @93
    cT
    cr
    @92
    wf
    @27
    wph
    @93
    wa
    cC
    cT
    @92
    cJ
    cK
    stoweidlem60.3
    stoweidlem60.4
    stoweidlem60.5
    wph
    cA
    cC
    @92
    stoweidlem60.10
    sselda
    fcnre
    3ad2antl1
    stoweidlem17
    syl3anc
    @104
    vt
    cB
    cD
    cT
    vi
    vj
    cE
    cF
    vt
    cT
    @2
    @36
    wcel
    #
    vj
    c1
    @18
    cfz
    co
    crab
    cmpt
    #
    @18
    @26
    stoweidlem60.1
    wph
    @44
    vj
    wph
    vj
    nfv
    @24
    @27
    @43
    vj
    @24
    vj
    nfv
    @27
    vj
    nfv
    @42
    vj
    @25
    nfra1
    nf3an
    nfan
    wph
    @44
    vt
    stoweidlem60.2
    @24
    @27
    @43
    vt
    @19
    @23
    vt
    @67
    @22
    vt
    cT
    nfra1
    nfan
    @117
    @42
    vt
    vj
    @25
    vt
    @25
    nfcv
    @33
    @37
    @41
    vt
    @32
    vt
    cT
    nfra1
    @35
    vt
    @36
    nfra1
    @39
    vt
    @40
    nfra1
    nf3an
    nfral
    nf3an
    nfan
    stoweidlem60.6
    stoweidlem60.7
    @120
    eqid
    @115
    wph
    cT
    cvv
    wcel
    @44
    wph
    cT
    cJ
    cuni
    #
    cvv
    stoweidlem60.4
    wph
    @91
    @121
    cvv
    wcel
    stoweidlem60.8
    cJ
    ccmp
    uniexg
    syl
    syl5eqel
    adantr
    wph
    cT
    cr
    cF
    wf
    @44
    @71
    adantr
    wph
    @68
    cc0
    @3
    cle
    wbr
    #
    @44
    wph
    @122
    vt
    cT
    stoweidlem60.16
    r19.21bi
    adantlr
    @104
    @22
    vt
    cT
    @19
    @23
    @27
    @43
    wph
    simpr1r
    r19.21bi
    wph
    @102
    @44
    stoweidlem60.17
    adantr
    wph
    @103
    @44
    stoweidlem60.18
    adantr
    @104
    @0
    @25
    wcel
    #
    wa
    wph
    @27
    @123
    cT
    cr
    @28
    wf
    #
    wph
    @44
    @123
    simpll
    @24
    @27
    @43
    wph
    @123
    simplr2
    @104
    @123
    simpr
    wph
    @27
    @123
    w3a
    wph
    @28
    cA
    wcel
    #
    @124
    wph
    @27
    @123
    simp1
    @27
    @123
    @125
    wph
    @25
    cA
    @0
    @26
    ffvelrn
    3adant1
    wph
    @125
    wa
    cC
    cT
    @28
    cJ
    cK
    stoweidlem60.3
    stoweidlem60.4
    stoweidlem60.5
    wph
    cA
    cC
    @28
    stoweidlem60.10
    sselda
    fcnre
    syl2anc
    syl3anc
    @104
    @123
    @68
    w3a
    #
    @30
    vt
    cT
    wral
    #
    vj
    @25
    wral
    #
    @123
    @68
    @30
    @126
    @43
    @33
    vj
    @25
    wral
    #
    @128
    @24
    @27
    @43
    wph
    @123
    @68
    simp1r3
    #
    @43
    @129
    @37
    vj
    @25
    wral
    #
    @41
    vj
    @25
    wral
    #
    @33
    @37
    @41
    vj
    @25
    r19.26-3
    #
    simp1bi
    #
    @32
    @30
    vj
    vt
    @25
    cT
    @30
    @31
    simpl
    2ralimi
    3syl
    @104
    @123
    @68
    simp2
    #
    @104
    @123
    @68
    simp3
    #
    @128
    @123
    wa
    @30
    vt
    cT
    @127
    vj
    @25
    rspa
    r19.21bi
    syl21anc
    @126
    @31
    vt
    cT
    wral
    #
    vj
    @25
    wral
    #
    @123
    @68
    @31
    @126
    @43
    @129
    @138
    @130
    @134
    @32
    @31
    vj
    vt
    @25
    cT
    @30
    @31
    simpr
    2ralimi
    3syl
    @135
    @136
    @138
    @123
    wa
    @31
    vt
    cT
    @137
    vj
    @25
    rspa
    r19.21bi
    syl21anc
    @104
    @123
    @119
    w3a
    #
    @131
    @123
    @119
    @35
    @139
    @43
    @131
    @24
    @27
    @43
    wph
    @123
    @119
    simp1r3
    @43
    @129
    @131
    @132
    @133
    simp2bi
    syl
    @104
    @123
    @119
    simp2
    @104
    @123
    @119
    simp3
    @131
    @123
    wa
    @35
    vt
    @36
    @37
    vj
    @25
    rspa
    r19.21bi
    syl21anc
    @104
    @123
    @2
    @40
    wcel
    #
    w3a
    #
    @132
    @123
    @140
    @39
    @141
    @43
    @132
    @24
    @27
    @43
    wph
    @123
    @140
    simp1r3
    @43
    @129
    @131
    @132
    @133
    simp3bi
    syl
    @104
    @123
    @140
    simp2
    @104
    @123
    @140
    simp3
    @132
    @123
    wa
    @39
    vt
    @40
    @41
    vj
    @25
    rspa
    r19.21bi
    syl21anc
    stoweidlem34
    @14
    @114
    vg
    @106
    cA
    @6
    @106
    wceq
    #
    @13
    @113
    vt
    cT
    vt
    @6
    @106
    vt
    cT
    @105
    nfmpt1
    nfeq2
    @142
    @12
    @112
    vj
    cr
    @142
    @11
    @111
    @5
    @142
    @9
    @109
    @10
    @110
    @142
    @7
    @108
    @8
    clt
    @2
    @6
    @106
    fveq1
    #
    breq1d
    @142
    @7
    @108
    @1
    clt
    @143
    breq2d
    anbi12d
    anbi2d
    rexbidv
    ralbid
    rspcev
    syl2anc
    ex
    2eximdv
    mpd
    wph
    @16
    @16
    vn
    wph
    @16
    idd
    exlimdv
    mpd
    wph
    @15
    @15
    vx
    wph
    @15
    idd
    exlimdv
    mpd
end
