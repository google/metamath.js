include "cmps.mm"
include "co.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cmulr.mm"
include "ctp.mm"
include "csca.mm"
include "cvsca.mm"
include "cts.mm"
include "cun.mm"
include "cvv.mm"
include "cv.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "cmin.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cmpt2.mm"
include "csn.mm"
include "ctopn.mm"
include "cpt.mm"
include "csb.mm"
include "wceq.mm"
include "df-psr.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "oveq2d.mm"
include "rabeq.mm"
include "syl.mm"
include "syl6eqr.mm"
include "csbeq1d.mm"
include "ovex.mm"
include "rabex.mm"
include "syl6eqelr.mm"
include "simplrr.mm"
include "fveq2d.mm"
include "simpr.mm"
include "oveq12d.mm"
include "ad2antrr.mm"
include "eqtr4d.mm"
include "opeq2d.mm"
include "adantr.mm"
include "ofeq.mm"
include "xpeq12d.mm"
include "reseq12d.mm"
include "oveqd.mm"
include "mpteq12dv.mm"
include "mpt2eq123dv.mm"
include "tpeq123d.mm"
include "xpeq1d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "sneqd.mm"
include "ad3antrrr.mm"
include "uneq12d.mm"
include "csbied.mm"
include "eqtrd.mm"
include "elex.mm"
include "tpex.mm"
include "unex.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem psrval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let c.xp: class .X.
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let cI: class I
  let cJ: class J
  let cK: class K
  let cO: class O
  let cW: class W
  let cX: class X
  let vi: setvar i
  let vr: setvar r
  let vb: setvar b
  let vd: setvar d
  assume psrval.s: |- S = ( I mPwSer R )
  assume psrval.k: |- K = ( Base ` R )
  assume psrval.a: |- .+ = ( +g ` R )
  assume psrval.m: |- .x. = ( .r ` R )
  assume psrval.o: |- O = ( TopOpen ` R )
  assume psrval.d: |- D = { h e. ( NN0 ^m I ) | ( `' h " NN ) e. Fin }
  assume psrval.b: |- ( ph -> B = ( K ^m D ) )
  assume psrval.p: |- .+b = ( oF .+ |` ( B X. B ) )
  assume psrval.t: |- .X. = ( f e. B , g e. B |-> ( k e. D |-> ( R gsum ( x e. { y e. D | y oR <_ k } |-> ( ( f ` x ) .x. ( g ` ( k oF - x ) ) ) ) ) ) )
  assume psrval.v: |- .xb = ( x e. K , f e. B |-> ( ( D X. { x } ) oF .x. f ) )
  assume psrval.j: |- ( ph -> J = ( Xt_ ` ( D X. { O } ) ) )
  assume psrval.i: |- ( ph -> I e. W )
  assume psrval.r: |- ( ph -> R e. X )

  disjoint h y
  disjoint f g
  disjoint f k
  disjoint f x
  disjoint f ph
  disjoint g k
  disjoint g x
  disjoint g ph
  disjoint k x
  disjoint k ph
  disjoint ph x
  disjoint B f
  disjoint B g
  disjoint B k
  disjoint B x
  disjoint f h
  disjoint I f
  disjoint g h
  disjoint I g
  disjoint h k
  disjoint h x
  disjoint I h
  disjoint I k
  disjoint I x
  disjoint R f
  disjoint R g
  disjoint R k
  disjoint R x
  disjoint f y
  disjoint D f
  disjoint g y
  disjoint D g
  disjoint k y
  disjoint D k
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint h i
  disjoint h r
  disjoint i r
  disjoint i y
  disjoint r y
  disjoint b d
  disjoint b i
  disjoint b r
  disjoint .+b b
  disjoint d i
  disjoint d r
  disjoint .+b d
  disjoint .+b i
  disjoint .+b r
  disjoint J b
  disjoint J d
  disjoint J i
  disjoint J r
  disjoint b f
  disjoint b g
  disjoint b k
  disjoint b x
  disjoint b ph
  disjoint d f
  disjoint d g
  disjoint d k
  disjoint d x
  disjoint d ph
  disjoint f i
  disjoint f r
  disjoint g i
  disjoint g r
  disjoint i k
  disjoint i x
  disjoint i ph
  disjoint k r
  disjoint r x
  disjoint ph r
  disjoint B b
  disjoint B d
  disjoint B i
  disjoint B r
  disjoint b h
  disjoint I b
  disjoint d h
  disjoint I d
  disjoint I i
  disjoint I r
  disjoint R b
  disjoint R d
  disjoint R i
  disjoint R r
  disjoint b y
  disjoint D b
  disjoint d y
  disjoint D d
  disjoint .X. b
  disjoint .X. d
  disjoint .X. i
  disjoint .X. r
  disjoint .xb b
  disjoint .xb d
  disjoint .xb i
  disjoint .xb r
  assert |- ( ph -> S = ( { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+b >. , <. ( .r ` ndx ) , .X. >. } u. { <. ( Scalar ` ndx ) , R >. , <. ( .s ` ndx ) , .xb >. , <. ( TopSet ` ndx ) , J >. } ) )

  proof
    wph
    cS
    cI
    cR
    cmps
    co
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    cnx
    cplusg
    cfv
    #
    c.pb
    cop
    #
    cnx
    cmulr
    cfv
    #
    c.xp
    cop
    #
    ctp
    #
    cnx
    csca
    cfv
    #
    cR
    cop
    #
    cnx
    cvsca
    cfv
    #
    c.xb
    cop
    #
    cnx
    cts
    cfv
    #
    cJ
    cop
    #
    ctp
    #
    cun
    #
    psrval.s
    wph
    vi
    vr
    cI
    cR
    cvv
    cvv
    vd
    vh
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vh
    cn0
    vi
    cv
    #
    cmap
    co
    #
    crab
    #
    vb
    vr
    cv
    #
    cbs
    cfv
    #
    vd
    cv
    #
    cmap
    co
    #
    @0
    vb
    cv
    #
    cop
    #
    @2
    @19
    cplusg
    cfv
    #
    cof
    #
    @23
    @23
    cxp
    #
    cres
    #
    cop
    #
    @4
    vf
    vg
    @23
    @23
    vk
    @21
    @19
    vx
    vy
    cv
    vk
    cv
    #
    cle
    cofr
    wbr
    #
    vy
    @21
    crab
    #
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    @30
    @33
    cmin
    cof
    co
    vg
    cv
    cfv
    #
    @19
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
    cmpt2
    #
    cop
    #
    ctp
    #
    @7
    @19
    cop
    #
    @9
    vx
    vf
    @20
    @23
    @21
    @33
    csn
    #
    cxp
    #
    @34
    @37
    cof
    #
    co
    #
    cmpt2
    #
    cop
    #
    @11
    @21
    @19
    ctopn
    cfv
    #
    csn
    #
    cxp
    #
    cpt
    cfv
    #
    cop
    #
    ctp
    #
    cun
    #
    csb
    #
    csb
    #
    @14
    cmps
    cvv
    cmps
    vi
    vr
    cvv
    cvv
    @60
    cmpt2
    wceq
    wph
    vx
    vy
    vf
    vg
    vh
    vi
    vk
    vr
    vb
    vd
    df-psr
    a1i
    wph
    @16
    cI
    wceq
    #
    @19
    cR
    wceq
    #
    wa
    #
    wa
    #
    @60
    vd
    cD
    @59
    csb
    @14
    @64
    vd
    @18
    cD
    @59
    @64
    @18
    @15
    vh
    cn0
    cI
    cmap
    co
    #
    crab
    #
    cD
    @64
    @17
    @65
    wceq
    @18
    @66
    wceq
    @64
    @16
    cI
    cn0
    cmap
    wph
    @61
    @62
    simprl
    oveq2d
    @15
    vh
    @17
    @65
    rabeq
    syl
    psrval.d
    syl6eqr
    #
    csbeq1d
    @64
    vd
    cD
    @59
    @14
    cvv
    @64
    cD
    @18
    cvv
    @67
    @15
    vh
    @17
    cn0
    @16
    cmap
    ovex
    rabex
    syl6eqelr
    @64
    @21
    cD
    wceq
    #
    wa
    #
    @59
    vb
    cB
    @58
    csb
    @14
    @69
    vb
    @22
    cB
    @58
    @69
    @22
    cK
    cD
    cmap
    co
    #
    cB
    @69
    @20
    cK
    @21
    cD
    cmap
    @69
    @20
    cR
    cbs
    cfv
    cK
    @69
    @19
    cR
    cbs
    wph
    @61
    @62
    @68
    simplrr
    #
    fveq2d
    psrval.k
    syl6eqr
    #
    @64
    @68
    simpr
    #
    oveq12d
    wph
    cB
    @70
    wceq
    @63
    @68
    psrval.b
    ad2antrr
    eqtr4d
    #
    csbeq1d
    @69
    vb
    cB
    @58
    @14
    cvv
    @69
    cB
    @22
    cvv
    @74
    @20
    @21
    cmap
    ovex
    syl6eqelr
    @69
    @23
    cB
    wceq
    #
    wa
    #
    @44
    @6
    @57
    @13
    @76
    @24
    @1
    @29
    @3
    @43
    @5
    @76
    @23
    cB
    @0
    @69
    @75
    simpr
    #
    opeq2d
    @76
    @28
    c.pb
    @2
    @76
    @28
    c.pl
    cof
    #
    cB
    cB
    cxp
    #
    cres
    c.pb
    @76
    @26
    @78
    @27
    @79
    @76
    @25
    c.pl
    wceq
    @26
    @78
    wceq
    @76
    @25
    cR
    cplusg
    cfv
    c.pl
    @76
    @19
    cR
    cplusg
    @69
    @62
    @75
    @71
    adantr
    #
    fveq2d
    psrval.a
    syl6eqr
    @25
    c.pl
    ofeq
    syl
    @76
    @23
    cB
    @23
    cB
    @77
    @77
    xpeq12d
    reseq12d
    psrval.p
    syl6eqr
    opeq2d
    @76
    @42
    c.xp
    @4
    @76
    @42
    vf
    vg
    cB
    cB
    vk
    cD
    cR
    vx
    @31
    vy
    cD
    crab
    #
    @35
    @36
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cmpt2
    c.xp
    @76
    vf
    vg
    @23
    @23
    @41
    cB
    cB
    @85
    @77
    @77
    @76
    vk
    @21
    @40
    cD
    @84
    @69
    @68
    @75
    @73
    adantr
    #
    @76
    @19
    cR
    @39
    @83
    cgsu
    @80
    @76
    vx
    @32
    @38
    @81
    @82
    @76
    @68
    @32
    @81
    wceq
    @86
    @31
    vy
    @21
    cD
    rabeq
    syl
    @76
    @37
    c.x
    @35
    @36
    @76
    @37
    cR
    cmulr
    cfv
    c.x
    @76
    @19
    cR
    cmulr
    @80
    fveq2d
    psrval.m
    syl6eqr
    #
    oveqd
    mpteq12dv
    oveq12d
    mpteq12dv
    mpt2eq123dv
    psrval.t
    syl6eqr
    opeq2d
    tpeq123d
    @76
    @45
    @8
    @51
    @10
    @56
    @12
    @76
    @19
    cR
    @7
    @80
    opeq2d
    @76
    @50
    c.xb
    @9
    @76
    @50
    vx
    vf
    cK
    cB
    cD
    @46
    cxp
    #
    @34
    c.x
    cof
    #
    co
    #
    cmpt2
    c.xb
    @76
    vx
    vf
    @20
    @23
    @49
    cK
    cB
    @90
    @69
    @20
    cK
    wceq
    @75
    @72
    adantr
    @77
    @76
    @47
    @88
    @34
    @34
    @48
    @89
    @76
    @37
    c.x
    wceq
    @48
    @89
    wceq
    @87
    @37
    c.x
    ofeq
    syl
    @76
    @21
    cD
    @46
    @86
    xpeq1d
    @76
    @34
    eqidd
    oveq123d
    mpt2eq123dv
    psrval.v
    syl6eqr
    opeq2d
    @76
    @55
    cJ
    @11
    @76
    @55
    cD
    cO
    csn
    #
    cxp
    #
    cpt
    cfv
    #
    cJ
    @76
    @54
    @92
    cpt
    @76
    @21
    cD
    @53
    @91
    @86
    @76
    @52
    cO
    @76
    @52
    cR
    ctopn
    cfv
    cO
    @76
    @19
    cR
    ctopn
    @80
    fveq2d
    psrval.o
    syl6eqr
    sneqd
    xpeq12d
    fveq2d
    wph
    cJ
    @93
    wceq
    @63
    @68
    @75
    psrval.j
    ad3antrrr
    eqtr4d
    opeq2d
    tpeq123d
    uneq12d
    csbied
    eqtrd
    csbied
    eqtrd
    wph
    cI
    cW
    wcel
    cI
    cvv
    wcel
    psrval.i
    cI
    cW
    elex
    syl
    wph
    cR
    cX
    wcel
    cR
    cvv
    wcel
    psrval.r
    cR
    cX
    elex
    syl
    @14
    cvv
    wcel
    wph
    @6
    @13
    @1
    @3
    @5
    tpex
    @8
    @10
    @12
    tpex
    unex
    a1i
    ovmpt2d
    syl5eq
end
