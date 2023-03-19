include "co.mm"
include "cfv.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "clt.mm"
include "c0g.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cofr.mm"
include "crab.mm"
include "cmin.mm"
include "cof.mm"
include "cmulr.mm"
include "cmpt.mm"
include "cgsu.mm"
include "eqid.mm"
include "mplmul.mm"
include "fveq1d.mm"
include "adantr.mm"
include "breq2.mm"
include "rabbidv.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "mpteq12dv.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ad2antrl.mm"
include "ad2antrr.mm"
include "elrabi.mm"
include "adantl.mm"
include "adantrr.mm"
include "cxr.mm"
include "w3a.mm"
include "mdegxrcl.mm"
include "syl.mm"
include "cn0.mm"
include "cr.mm"
include "nn0ssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "sseldi.mm"
include "wf.mm"
include "tdeglem1.mm"
include "ffvelrnd.mm"
include "3jca.mm"
include "anim1i.mm"
include "anasss.mm"
include "xrlelttr.mm"
include "sylc.mm"
include "mdeglt.mm"
include "oveq1d.mm"
include "crg.mm"
include "cbs.mm"
include "mplelf.mm"
include "ssrab2.mm"
include "simplrl.mm"
include "simpr.mm"
include "psrbagconcl.mm"
include "syl3anc.mm"
include "ringlz.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "anassrs.mm"
include "ringrz.mm"
include "wo.mm"
include "simplrr.mm"
include "wn.mm"
include "nn0red.mm"
include "le2add.mm"
include "syl22anc.mm"
include "tdeglem3.mm"
include "psrbagf.mm"
include "3adant3.mm"
include "ffvelrnda.mm"
include "nn0cnd.mm"
include "3adant2.mm"
include "pncan3d.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "simp1.mm"
include "fvexd.mm"
include "ovexd.mm"
include "feqmptd.mm"
include "offval2.mm"
include "3eqtr4d.mm"
include "eqtr3d.mm"
include "breq1d.mm"
include "sylibd.mm"
include "lenltd.mm"
include "anbi12d.mm"
include "ioran.mm"
include "syl6bbr.mm"
include "nn0addcld.mm"
include "3imtr3d.mm"
include "mt4d.mm"
include "mpjaodan.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cmap.mm"
include "rab2ex.mm"
include "gsumz.mm"
include "sylancl.mm"
include "3eqtrd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "wb.mm"
include "mplring.mm"
include "ringcl.mm"
include "mdegleb.mm"
include "mpbird.mm"

theorem mdegmullem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cV: class V
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vx: setvar x
  assume mdegaddle.y: |- Y = ( I mPoly R )
  assume mdegaddle.d: |- D = ( I mDeg R )
  assume mdegaddle.i: |- ( ph -> I e. V )
  assume mdegaddle.r: |- ( ph -> R e. Ring )
  assume mdegmulle2.b: |- B = ( Base ` Y )
  assume mdegmulle2.t: |- .x. = ( .r ` Y )
  assume mdegmulle2.f: |- ( ph -> F e. B )
  assume mdegmulle2.g: |- ( ph -> G e. B )
  assume mdegmulle2.j1: |- ( ph -> J e. NN0 )
  assume mdegmulle2.k1: |- ( ph -> K e. NN0 )
  assume mdegmulle2.j2: |- ( ph -> ( D ` F ) <_ J )
  assume mdegmulle2.k2: |- ( ph -> ( D ` G ) <_ K )
  assume mdegmullem.a: |- A = { a e. ( NN0 ^m I ) | ( `' a " NN ) e. Fin }
  assume mdegmullem.h: |- H = ( b e. A |-> ( CCfld gsum b ) )

  disjoint A b
  disjoint I a
  disjoint I b
  disjoint a b
  disjoint R b
  disjoint V b
  disjoint A c
  disjoint A d
  disjoint A e
  disjoint A x
  disjoint H d
  disjoint H x
  disjoint V e
  disjoint c ph
  disjoint d ph
  disjoint ph x
  disjoint c d
  disjoint c x
  disjoint d x
  disjoint B x
  disjoint F c
  disjoint F d
  disjoint F x
  disjoint G c
  disjoint G d
  disjoint G x
  disjoint I d
  disjoint I x
  disjoint a d
  disjoint a x
  disjoint b d
  disjoint b x
  disjoint I c
  disjoint I e
  disjoint c e
  disjoint J d
  disjoint J x
  disjoint K d
  disjoint K x
  disjoint R d
  disjoint R x
  disjoint R c
  disjoint .x. x
  disjoint a c
  disjoint a e
  disjoint d e
  disjoint e x
  assert |- ( ph -> ( D ` ( F .x. G ) ) <_ ( J + K ) )

  proof
    wph
    cF
    cG
    c.x
    co
    #
    cD
    cfv
    cJ
    cK
    caddc
    co
    #
    cle
    wbr
    #
    @1
    vx
    cv
    #
    cH
    cfv
    #
    clt
    wbr
    #
    @3
    @0
    cfv
    #
    cR
    c0g
    cfv
    #
    wceq
    #
    wi
    #
    vx
    cA
    wral
    #
    wph
    @9
    vx
    cA
    wph
    @3
    cA
    wcel
    #
    @5
    @8
    wph
    @11
    @5
    wa
    #
    wa
    #
    @6
    @3
    vc
    cA
    cR
    vd
    ve
    cv
    #
    vc
    cv
    #
    cle
    cofr
    #
    wbr
    #
    ve
    cA
    crab
    #
    vd
    cv
    #
    cF
    cfv
    #
    @15
    @19
    cmin
    cof
    #
    co
    #
    cG
    cfv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cfv
    #
    cR
    vd
    @14
    @3
    @16
    wbr
    #
    ve
    cA
    crab
    #
    @20
    @3
    @19
    @21
    co
    #
    cG
    cfv
    #
    @24
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @7
    wph
    @6
    @29
    wceq
    @12
    wph
    @3
    @0
    @28
    wph
    vd
    ve
    cB
    cA
    cY
    cR
    c.x
    @24
    va
    vc
    cF
    cG
    cI
    mdegaddle.y
    mdegmulle2.b
    @24
    eqid
    #
    mdegmulle2.t
    mdegmullem.a
    mdegmulle2.f
    mdegmulle2.g
    mplmul
    fveq1d
    adantr
    @11
    @29
    @36
    wceq
    wph
    @5
    vc
    @3
    @27
    @36
    cA
    @28
    @15
    @3
    wceq
    #
    @26
    @35
    cR
    cgsu
    @38
    vd
    @18
    @25
    @31
    @34
    @38
    @17
    @30
    ve
    cA
    @15
    @3
    @14
    @16
    breq2
    rabbidv
    @38
    @23
    @33
    @20
    @24
    @38
    @22
    @32
    cG
    @15
    @3
    @19
    @21
    oveq1
    fveq2d
    oveq2d
    mpteq12dv
    oveq2d
    @28
    eqid
    cR
    @35
    cgsu
    ovex
    fvmpt
    ad2antrl
    @13
    @36
    cR
    vd
    @31
    @7
    cmpt
    #
    cgsu
    co
    #
    @7
    @13
    @35
    @39
    cR
    cgsu
    @13
    vd
    @31
    @34
    @7
    @13
    @19
    @31
    wcel
    #
    wa
    #
    cJ
    @19
    cH
    cfv
    #
    clt
    wbr
    #
    @34
    @7
    wceq
    #
    cK
    @32
    cH
    cfv
    #
    clt
    wbr
    #
    @13
    @41
    @44
    @45
    @13
    @41
    @44
    wa
    #
    wa
    #
    @34
    @7
    @33
    @24
    co
    #
    @7
    @49
    @20
    @7
    @33
    @24
    @49
    cA
    cB
    cD
    cY
    cR
    vb
    va
    cF
    cH
    cI
    @19
    @7
    mdegaddle.d
    mdegaddle.y
    mdegmulle2.b
    @7
    eqid
    #
    mdegmullem.a
    mdegmullem.h
    wph
    cF
    cB
    wcel
    #
    @12
    @48
    mdegmulle2.f
    ad2antrr
    @13
    @41
    @19
    cA
    wcel
    #
    @44
    @41
    @53
    @13
    @30
    ve
    @19
    cA
    elrabi
    adantl
    #
    adantrr
    @49
    cF
    cD
    cfv
    #
    cxr
    wcel
    #
    cJ
    cxr
    wcel
    #
    @43
    cxr
    wcel
    #
    w3a
    #
    @55
    cJ
    cle
    wbr
    #
    @44
    wa
    #
    @55
    @43
    clt
    wbr
    @13
    @41
    @59
    @44
    @42
    @56
    @57
    @58
    wph
    @56
    @12
    @41
    wph
    @52
    @56
    mdegmulle2.f
    cB
    cD
    cY
    cR
    cF
    cI
    mdegaddle.d
    mdegaddle.y
    mdegmulle2.b
    mdegxrcl
    syl
    ad2antrr
    wph
    @57
    @12
    @41
    wph
    cn0
    cxr
    cJ
    cn0
    cr
    cxr
    nn0ssre
    ressxr
    sstri
    #
    mdegmulle2.j1
    sseldi
    ad2antrr
    @42
    cn0
    cxr
    @43
    @62
    @42
    cA
    cn0
    @19
    cH
    wph
    cA
    cn0
    cH
    wf
    #
    @12
    @41
    wph
    cI
    cV
    wcel
    #
    @63
    mdegaddle.i
    cA
    vb
    va
    cH
    cI
    cV
    mdegmullem.a
    mdegmullem.h
    tdeglem1
    syl
    ad2antrr
    #
    @54
    ffvelrnd
    #
    sseldi
    3jca
    adantrr
    @13
    @41
    @44
    @61
    @42
    @60
    @44
    wph
    @60
    @12
    @41
    mdegmulle2.j2
    ad2antrr
    anim1i
    anasss
    @55
    cJ
    @43
    xrlelttr
    sylc
    mdeglt
    oveq1d
    @13
    @41
    @50
    @7
    wceq
    #
    @44
    @42
    cR
    crg
    wcel
    #
    @33
    cR
    cbs
    cfv
    #
    wcel
    @67
    wph
    @68
    @12
    @41
    mdegaddle.r
    ad2antrr
    #
    @42
    cA
    @69
    @32
    cG
    wph
    cA
    @69
    cG
    wf
    @12
    @41
    wph
    cB
    cA
    cY
    cR
    va
    cI
    @69
    cG
    mdegaddle.y
    @69
    eqid
    #
    mdegmulle2.b
    mdegmullem.a
    mdegmulle2.g
    mplelf
    ad2antrr
    @42
    @31
    cA
    @32
    @30
    ve
    cA
    ssrab2
    @42
    @64
    @11
    @41
    @32
    @31
    wcel
    wph
    @64
    @12
    @41
    mdegaddle.i
    ad2antrr
    #
    wph
    @11
    @5
    @41
    simplrl
    #
    @13
    @41
    simpr
    ve
    cA
    @31
    va
    @3
    cI
    cV
    @19
    mdegmullem.a
    @31
    eqid
    psrbagconcl
    syl3anc
    sseldi
    #
    ffvelrnd
    @69
    cR
    @24
    @33
    @7
    @71
    @37
    @51
    ringlz
    syl2anc
    adantrr
    eqtrd
    anassrs
    @13
    @41
    @47
    @45
    @13
    @41
    @47
    wa
    #
    wa
    #
    @34
    @20
    @7
    @24
    co
    #
    @7
    @76
    @33
    @7
    @20
    @24
    @76
    cA
    cB
    cD
    cY
    cR
    vb
    va
    cG
    cH
    cI
    @32
    @7
    mdegaddle.d
    mdegaddle.y
    mdegmulle2.b
    @51
    mdegmullem.a
    mdegmullem.h
    wph
    cG
    cB
    wcel
    #
    @12
    @75
    mdegmulle2.g
    ad2antrr
    @13
    @41
    @32
    cA
    wcel
    #
    @47
    @74
    adantrr
    @76
    cG
    cD
    cfv
    #
    cxr
    wcel
    #
    cK
    cxr
    wcel
    #
    @46
    cxr
    wcel
    #
    w3a
    #
    @80
    cK
    cle
    wbr
    #
    @47
    wa
    #
    @80
    @46
    clt
    wbr
    @13
    @41
    @84
    @47
    @42
    @81
    @82
    @83
    wph
    @81
    @12
    @41
    wph
    @78
    @81
    mdegmulle2.g
    cB
    cD
    cY
    cR
    cG
    cI
    mdegaddle.d
    mdegaddle.y
    mdegmulle2.b
    mdegxrcl
    syl
    ad2antrr
    wph
    @82
    @12
    @41
    wph
    cn0
    cxr
    cK
    @62
    mdegmulle2.k1
    sseldi
    ad2antrr
    @42
    cn0
    cxr
    @46
    @62
    @42
    cA
    cn0
    @32
    cH
    @65
    @74
    ffvelrnd
    #
    sseldi
    3jca
    adantrr
    @13
    @41
    @47
    @86
    @42
    @85
    @47
    wph
    @85
    @12
    @41
    mdegmulle2.k2
    ad2antrr
    anim1i
    anasss
    @80
    cK
    @46
    xrlelttr
    sylc
    mdeglt
    oveq2d
    @13
    @41
    @77
    @7
    wceq
    #
    @47
    @42
    @68
    @20
    @69
    wcel
    @88
    @70
    @42
    cA
    @69
    @19
    cF
    wph
    cA
    @69
    cF
    wf
    @12
    @41
    wph
    cB
    cA
    cY
    cR
    va
    cI
    @69
    cF
    mdegaddle.y
    @71
    mdegmulle2.b
    mdegmullem.a
    mdegmulle2.f
    mplelf
    ad2antrr
    @54
    ffvelrnd
    @69
    cR
    @24
    @20
    @7
    @71
    @37
    @51
    ringrz
    syl2anc
    adantrr
    eqtrd
    anassrs
    @42
    @5
    @44
    @47
    wo
    #
    wph
    @11
    @5
    @41
    simplrr
    @42
    @43
    cJ
    cle
    wbr
    #
    @46
    cK
    cle
    wbr
    #
    wa
    #
    @4
    @1
    cle
    wbr
    #
    @89
    wn
    #
    @5
    wn
    @42
    @92
    @43
    @46
    caddc
    co
    #
    @1
    cle
    wbr
    #
    @93
    @42
    @43
    cr
    wcel
    @46
    cr
    wcel
    cJ
    cr
    wcel
    cK
    cr
    wcel
    @92
    @96
    wi
    @42
    @43
    @66
    nn0red
    #
    @42
    @46
    @87
    nn0red
    #
    @42
    cJ
    wph
    cJ
    cn0
    wcel
    @12
    @41
    mdegmulle2.j1
    ad2antrr
    nn0red
    #
    @42
    cK
    wph
    cK
    cn0
    wcel
    @12
    @41
    mdegmulle2.k1
    ad2antrr
    nn0red
    #
    @43
    @46
    cJ
    cK
    le2add
    syl22anc
    @42
    @95
    @4
    @1
    cle
    @42
    @19
    @32
    caddc
    cof
    co
    #
    cH
    cfv
    #
    @95
    @4
    @42
    @64
    @53
    @79
    @102
    @95
    wceq
    @72
    @54
    @74
    cA
    vb
    va
    cH
    cI
    cV
    @19
    @32
    mdegmullem.a
    mdegmullem.h
    tdeglem3
    syl3anc
    @42
    @101
    @3
    cH
    @42
    @64
    @53
    @11
    @101
    @3
    wceq
    @72
    @54
    @73
    @64
    @53
    @11
    w3a
    #
    vb
    cI
    vb
    cv
    #
    @19
    cfv
    #
    @104
    @3
    cfv
    #
    @105
    cmin
    co
    #
    caddc
    co
    #
    cmpt
    vb
    cI
    @106
    cmpt
    @101
    @3
    @103
    vb
    cI
    @108
    @106
    @103
    @104
    cI
    wcel
    wa
    #
    @105
    @106
    @109
    @105
    @103
    cI
    cn0
    @104
    @19
    @64
    @53
    cI
    cn0
    @19
    wf
    @11
    cA
    va
    @19
    cI
    cV
    mdegmullem.a
    psrbagf
    3adant3
    #
    ffvelrnda
    nn0cnd
    @109
    @106
    @103
    cI
    cn0
    @104
    @3
    @64
    @11
    cI
    cn0
    @3
    wf
    @53
    cA
    va
    @3
    cI
    cV
    mdegmullem.a
    psrbagf
    3adant2
    #
    ffvelrnda
    nn0cnd
    pncan3d
    mpteq2dva
    @103
    vb
    cI
    @105
    @107
    caddc
    @19
    @32
    cV
    cvv
    cvv
    @64
    @53
    @11
    simp1
    #
    @109
    @104
    @19
    fvexd
    #
    @109
    @106
    @105
    cmin
    ovexd
    @103
    vb
    cI
    cn0
    @19
    @110
    feqmptd
    #
    @103
    vb
    cI
    @106
    @105
    cmin
    @3
    @19
    cV
    cvv
    cvv
    @112
    @109
    @104
    @3
    fvexd
    @113
    @103
    vb
    cI
    cn0
    @3
    @111
    feqmptd
    #
    @114
    offval2
    offval2
    @115
    3eqtr4d
    syl3anc
    fveq2d
    eqtr3d
    breq1d
    sylibd
    @42
    @92
    @44
    wn
    #
    @47
    wn
    #
    wa
    @94
    @42
    @90
    @116
    @91
    @117
    @42
    @43
    cJ
    @97
    @99
    lenltd
    @42
    @46
    cK
    @98
    @100
    lenltd
    anbi12d
    @44
    @47
    ioran
    syl6bbr
    @42
    @4
    @1
    @42
    @4
    @42
    cA
    cn0
    @3
    cH
    @65
    @73
    ffvelrnd
    nn0red
    @42
    @1
    wph
    @1
    cn0
    wcel
    @12
    @41
    wph
    cJ
    cK
    mdegmulle2.j1
    mdegmulle2.k1
    nn0addcld
    #
    ad2antrr
    nn0red
    lenltd
    3imtr3d
    mt4d
    mpjaodan
    mpteq2dva
    oveq2d
    @13
    cR
    cmnd
    wcel
    #
    @31
    cvv
    wcel
    @40
    @7
    wceq
    wph
    @119
    @12
    wph
    @68
    @119
    mdegaddle.r
    cR
    ringmnd
    syl
    adantr
    @30
    va
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    ve
    va
    cn0
    cI
    cmap
    co
    cA
    mdegmullem.a
    cn0
    cI
    cmap
    ovex
    rab2ex
    @31
    vd
    cR
    cvv
    @7
    @51
    gsumz
    sylancl
    eqtrd
    3eqtrd
    expr
    ralrimiva
    wph
    @0
    cB
    wcel
    #
    @1
    cxr
    wcel
    @2
    @10
    wb
    wph
    cY
    crg
    wcel
    #
    @52
    @78
    @120
    wph
    @64
    @68
    @121
    mdegaddle.i
    mdegaddle.r
    cY
    cR
    cI
    cV
    mdegaddle.y
    mplring
    syl2anc
    mdegmulle2.f
    mdegmulle2.g
    cB
    cY
    c.x
    cF
    cG
    mdegmulle2.b
    mdegmulle2.t
    ringcl
    syl3anc
    wph
    cn0
    cxr
    @1
    @62
    @118
    sseldi
    vx
    cA
    cB
    cD
    cY
    cR
    vb
    va
    @0
    @1
    cH
    cI
    @7
    mdegaddle.d
    mdegaddle.y
    mdegmulle2.b
    @51
    mdegmullem.a
    mdegmullem.h
    mdegleb
    syl2anc
    mpbird
end
