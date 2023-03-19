include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "co.mm"
include "cn.mm"
include "cmpt.mm"
include "csumge0.mm"
include "wa.mm"
include "cc0.mm"
include "nfv.mm"
include "nfre1.mm"
include "nfan.mm"
include "cfn.mm"
include "wcel.mm"
include "csn.mm"
include "cun.mm"
include "wss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "snfi.mm"
include "a1i.mm"
include "unfi.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "cr.mm"
include "wf.mm"
include "simpr.mm"
include "hoidmvval0.mm"
include "cvv.mm"
include "nnex.mm"
include "cpnf.mm"
include "cicc.mm"
include "cico.mm"
include "icossicc.mm"
include "cmap.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "syl.mm"
include "hoidmvcl.mm"
include "sseldi.mm"
include "eqid.mm"
include "fmptd.mm"
include "sge0ge0.mm"
include "eqbrtrd.mm"
include "wn.mm"
include "wceq.mm"
include "cxr.mm"
include "icossxr.mm"
include "sge0xrcl.mm"
include "clt.mm"
include "rge0ssre.mm"
include "ltpnf.mm"
include "id.mm"
include "eqcomd.mm"
include "adantl.mm"
include "breqtrd.mm"
include "xrltled.mm"
include "adantlr.mm"
include "wral.mm"
include "simpll.mm"
include "wb.mm"
include "ltnled.mm"
include "ralbidva.mm"
include "ralnex.mm"
include "bitrd.mm"
include "mpbird.mm"
include "sge0repnf.mm"
include "c1.mm"
include "caddc.mm"
include "cmul.mm"
include "crp.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "cbvmptv.mm"
include "fveq2i.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "cres.mm"
include "cmin.mm"
include "cif.mm"
include "crab.mm"
include "csup.mm"
include "ad3antrrr.mm"
include "c0.mm"
include "wne.mm"
include "cdif.mm"
include "breq12d.mm"
include "cbvralv.mm"
include "rspa.mm"
include "ad5ant25.mm"
include "biimpri.mm"
include "fveq1.mm"
include "breq1d.mm"
include "ifbieq1d.mm"
include "ifeq12d.mm"
include "mpteq2dv.mm"
include "eleq1.mm"
include "ifbieq12d.mm"
include "eqtrd.mm"
include "mpteq2i.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "breq2.mm"
include "eqidd.mm"
include "ifeq2d.mm"
include "fveq12d.mm"
include "fveq1d.mm"
include "fveq2d.mm"
include "cbvrabv.mm"
include "cixp.mm"
include "ciun.mm"
include "wi.mm"
include "hoidmvlelem4.mm"
include "syl21anc.mm"
include "ralrimiva.mm"
include "ad2antrr.mm"
include "0xr.mm"
include "pnfxr.mm"
include "elicod.mm"
include "xralrple2.mm"
include "pm2.61dan.mm"

theorem hoidmvlelem5
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vj: setvar j
  let vk: setvar k
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vc: setvar c
  let vw: setvar w
  let vz: setvar z
  let vi: setvar i
  let vl: setvar l
  let vd: setvar d
  assume hoidmvlelem5.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume hoidmvlelem5.f: |- ( ph -> X e. Fin )
  assume hoidmvlelem5.y: |- ( ph -> Y C_ X )
  assume hoidmvlelem5.z: |- ( ph -> Z e. ( X \ Y ) )
  assume hoidmvlelem5.w: |- W = ( Y u. { Z } )
  assume hoidmvlelem5.a: |- ( ph -> A : W --> RR )
  assume hoidmvlelem5.b: |- ( ph -> B : W --> RR )
  assume hoidmvlelem5.c: |- ( ph -> C : NN --> ( RR ^m W ) )
  assume hoidmvlelem5.d: |- ( ph -> D : NN --> ( RR ^m W ) )
  assume hoidmvlelem5.i: |- ( ph -> A. e e. ( RR ^m Y ) A. f e. ( RR ^m Y ) A. g e. ( ( RR ^m Y ) ^m NN ) A. h e. ( ( RR ^m Y ) ^m NN ) ( X_ k e. Y ( ( e ` k ) [,) ( f ` k ) ) C_ U_ j e. NN X_ k e. Y ( ( ( g ` j ) ` k ) [,) ( ( h ` j ) ` k ) ) -> ( e ( L ` Y ) f ) <_ ( sum^ ` ( j e. NN |-> ( ( g ` j ) ( L ` Y ) ( h ` j ) ) ) ) ) )
  assume hoidmvlelem5.s: |- ( ph -> X_ k e. W ( ( A ` k ) [,) ( B ` k ) ) C_ U_ j e. NN X_ k e. W ( ( ( C ` j ) ` k ) [,) ( ( D ` j ) ` k ) ) )
  assume hoidmvlelem5.n: |- ( ph -> Y =/= (/) )

  disjoint A a
  disjoint A b
  disjoint A h
  disjoint A j
  disjoint A k
  disjoint A x
  disjoint a b
  disjoint a h
  disjoint a j
  disjoint a k
  disjoint a x
  disjoint b h
  disjoint b j
  disjoint b k
  disjoint b x
  disjoint h j
  disjoint h k
  disjoint h x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint A e
  disjoint A f
  disjoint A g
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e j
  disjoint e k
  disjoint f g
  disjoint f h
  disjoint f j
  disjoint f k
  disjoint g h
  disjoint g j
  disjoint g k
  disjoint B a
  disjoint B b
  disjoint B h
  disjoint B j
  disjoint B k
  disjoint B x
  disjoint B f
  disjoint B g
  disjoint C a
  disjoint C b
  disjoint C h
  disjoint C j
  disjoint C k
  disjoint C x
  disjoint C g
  disjoint D a
  disjoint D b
  disjoint D h
  disjoint D j
  disjoint D k
  disjoint D x
  disjoint D g
  disjoint L a
  disjoint L b
  disjoint L h
  disjoint L j
  disjoint L k
  disjoint L x
  disjoint L e
  disjoint L f
  disjoint L g
  disjoint W a
  disjoint W b
  disjoint W h
  disjoint W j
  disjoint W k
  disjoint W x
  disjoint W g
  disjoint Y a
  disjoint Y b
  disjoint Y h
  disjoint Y j
  disjoint Y k
  disjoint Y x
  disjoint Y e
  disjoint Y f
  disjoint Y g
  disjoint Z a
  disjoint Z b
  disjoint Z h
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint Z g
  disjoint a ph
  disjoint b ph
  disjoint h ph
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  disjoint A r
  disjoint A s
  disjoint a r
  disjoint a s
  disjoint b r
  disjoint b s
  disjoint h r
  disjoint h s
  disjoint j r
  disjoint j s
  disjoint k r
  disjoint k s
  disjoint r s
  disjoint r x
  disjoint s x
  disjoint A c
  disjoint c h
  disjoint c j
  disjoint c k
  disjoint c r
  disjoint c s
  disjoint c x
  disjoint A w
  disjoint a w
  disjoint b w
  disjoint h w
  disjoint j w
  disjoint k w
  disjoint r w
  disjoint w x
  disjoint A z
  disjoint h z
  disjoint j z
  disjoint r z
  disjoint w z
  disjoint x z
  disjoint B r
  disjoint B s
  disjoint B c
  disjoint B w
  disjoint B z
  disjoint C i
  disjoint C l
  disjoint C w
  disjoint a i
  disjoint a l
  disjoint b i
  disjoint b l
  disjoint h i
  disjoint h l
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i w
  disjoint i x
  disjoint j l
  disjoint k l
  disjoint l w
  disjoint l x
  disjoint C c
  disjoint c i
  disjoint c l
  disjoint c w
  disjoint g i
  disjoint g l
  disjoint g w
  disjoint C r
  disjoint C z
  disjoint i z
  disjoint l z
  disjoint D i
  disjoint D l
  disjoint D w
  disjoint D c
  disjoint D r
  disjoint D z
  disjoint L i
  disjoint L l
  disjoint L w
  disjoint L c
  disjoint L r
  disjoint L z
  disjoint W d
  disjoint W i
  disjoint W l
  disjoint W w
  disjoint a d
  disjoint b d
  disjoint d h
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d l
  disjoint d w
  disjoint d x
  disjoint W c
  disjoint c d
  disjoint d g
  disjoint W r
  disjoint W s
  disjoint W z
  disjoint d z
  disjoint Y d
  disjoint Y i
  disjoint Y l
  disjoint Y w
  disjoint Y c
  disjoint Y z
  disjoint Z w
  disjoint Z c
  disjoint Z z
  disjoint ph r
  disjoint ph s
  disjoint c ph
  disjoint g r
  assert |- ( ph -> ( A ( L ` W ) B ) <_ ( sum^ ` ( j e. NN |-> ( ( C ` j ) ( L ` W ) ( D ` j ) ) ) ) )

  proof
    wph
    vs
    cv
    #
    cB
    cfv
    #
    @0
    cA
    cfv
    #
    cle
    wbr
    #
    vs
    cW
    wrex
    #
    cA
    cB
    cW
    cL
    cfv
    #
    co
    #
    vj
    cn
    vj
    cv
    #
    cC
    cfv
    #
    @7
    cD
    cfv
    #
    @5
    co
    #
    cmpt
    #
    csumge0
    cfv
    #
    cle
    wbr
    #
    wph
    @4
    wa
    #
    @6
    cc0
    @12
    cle
    @14
    vx
    cA
    cB
    vs
    vk
    cL
    cW
    va
    vb
    wph
    @4
    vs
    wph
    vs
    nfv
    @3
    vs
    cW
    nfre1
    nfan
    hoidmvlelem5.l
    wph
    cW
    cfn
    wcel
    #
    @4
    wph
    cW
    cY
    cZ
    csn
    #
    cun
    #
    cfn
    hoidmvlelem5.w
    wph
    cY
    cfn
    wcel
    #
    @16
    cfn
    wcel
    #
    @17
    cfn
    wcel
    wph
    cX
    cfn
    wcel
    #
    cY
    cX
    wss
    #
    @18
    hoidmvlelem5.f
    hoidmvlelem5.y
    cX
    cY
    ssfi
    syl2anc
    @19
    wph
    cZ
    snfi
    a1i
    cY
    @16
    unfi
    syl2anc
    syl5eqel
    #
    adantr
    wph
    cW
    cr
    cA
    wf
    #
    @4
    hoidmvlelem5.a
    adantr
    wph
    cW
    cr
    cB
    wf
    #
    @4
    hoidmvlelem5.b
    adantr
    wph
    @4
    simpr
    hoidmvval0
    wph
    cc0
    @12
    cle
    wbr
    #
    @4
    wph
    @11
    cvv
    cn
    cn
    cvv
    wcel
    #
    wph
    nnex
    a1i
    #
    wph
    vj
    cn
    @10
    cc0
    cpnf
    cicc
    co
    #
    @11
    wph
    @7
    cn
    wcel
    #
    wa
    #
    cc0
    cpnf
    cico
    co
    #
    @28
    @10
    cc0
    cpnf
    icossicc
    @30
    vx
    @8
    @9
    vk
    cL
    cW
    va
    vb
    hoidmvlelem5.l
    wph
    @15
    @29
    @22
    adantr
    @30
    @8
    cr
    cW
    cmap
    co
    #
    wcel
    cW
    cr
    @8
    wf
    wph
    cn
    @32
    @7
    cC
    hoidmvlelem5.c
    ffvelrnda
    @8
    cr
    cW
    elmapi
    syl
    @30
    @9
    @32
    wcel
    cW
    cr
    @9
    wf
    wph
    cn
    @32
    @7
    cD
    hoidmvlelem5.d
    ffvelrnda
    @9
    cr
    cW
    elmapi
    syl
    hoidmvcl
    sseldi
    @11
    eqid
    fmptd
    #
    sge0ge0
    #
    adantr
    eqbrtrd
    wph
    @4
    wn
    #
    wa
    #
    @12
    cpnf
    wceq
    #
    @13
    wph
    @37
    @13
    @35
    wph
    @37
    wa
    #
    @6
    @12
    wph
    @6
    cxr
    wcel
    #
    @37
    wph
    @31
    cxr
    @6
    cc0
    cpnf
    icossxr
    wph
    vx
    cA
    cB
    vk
    cL
    cW
    va
    vb
    hoidmvlelem5.l
    @22
    hoidmvlelem5.a
    hoidmvlelem5.b
    hoidmvcl
    #
    sseldi
    #
    adantr
    wph
    @12
    cxr
    wcel
    #
    @37
    wph
    @11
    cvv
    cn
    @27
    @33
    sge0xrcl
    #
    adantr
    @38
    @6
    cpnf
    @12
    clt
    wph
    @6
    cpnf
    clt
    wbr
    #
    @37
    wph
    @6
    cr
    wcel
    @44
    wph
    @31
    cr
    @6
    rge0ssre
    @40
    sseldi
    @6
    ltpnf
    syl
    adantr
    @37
    cpnf
    @12
    wceq
    wph
    @37
    @12
    cpnf
    @37
    id
    eqcomd
    adantl
    breqtrd
    xrltled
    adantlr
    @36
    @37
    wn
    #
    wa
    wph
    @2
    @1
    clt
    wbr
    #
    vs
    cW
    wral
    #
    @12
    cr
    wcel
    #
    @13
    wph
    @35
    @45
    simpll
    @36
    @47
    @45
    @36
    @47
    @35
    wph
    @35
    simpr
    wph
    @47
    @35
    wb
    @35
    wph
    @47
    @3
    wn
    #
    vs
    cW
    wral
    #
    @35
    wph
    @46
    @49
    vs
    cW
    wph
    @0
    cW
    wcel
    wa
    @2
    @1
    wph
    cW
    cr
    @0
    cA
    hoidmvlelem5.a
    ffvelrnda
    wph
    cW
    cr
    @0
    cB
    hoidmvlelem5.b
    ffvelrnda
    ltnled
    ralbidva
    @50
    @35
    wb
    wph
    @3
    vs
    cW
    ralnex
    a1i
    bitrd
    adantr
    mpbird
    adantr
    wph
    @45
    @48
    @35
    wph
    @45
    wa
    #
    @48
    @45
    wph
    @45
    simpr
    @51
    @11
    cvv
    cn
    @26
    @51
    nnex
    a1i
    wph
    cn
    @28
    @11
    wf
    @45
    @33
    adantr
    sge0repnf
    mpbird
    adantlr
    wph
    @47
    wa
    #
    @48
    wa
    #
    @13
    @6
    c1
    vr
    cv
    #
    caddc
    co
    #
    @12
    cmul
    co
    cle
    wbr
    #
    vr
    crp
    wral
    @53
    @56
    vr
    crp
    @53
    @54
    crp
    wcel
    #
    wa
    @52
    vi
    cn
    vi
    cv
    #
    cC
    cfv
    #
    @58
    cD
    cfv
    #
    @5
    co
    #
    cmpt
    #
    csumge0
    cfv
    #
    cr
    wcel
    #
    @57
    @56
    @52
    @48
    @57
    simpll
    @48
    @64
    @52
    @57
    @48
    @64
    @12
    @63
    cr
    @11
    @62
    csumge0
    vj
    vi
    cn
    @10
    @61
    @7
    @58
    wceq
    @8
    @59
    @9
    @60
    @5
    @7
    @58
    cC
    fveq2
    @7
    @58
    cD
    fveq2
    oveq12d
    cbvmptv
    fveq2i
    eleq1i
    #
    biimpi
    ad2antlr
    @53
    @57
    simpr
    @52
    @64
    wa
    #
    @57
    wa
    vx
    vz
    cA
    cB
    cC
    cD
    cA
    cY
    cres
    cB
    cY
    cres
    cY
    cL
    cfv
    #
    co
    #
    vw
    cv
    #
    cZ
    cA
    cfv
    #
    cmin
    co
    #
    cmul
    co
    #
    @55
    vl
    cn
    vl
    cv
    #
    cC
    cfv
    #
    @73
    cD
    cfv
    #
    @69
    vw
    cr
    vd
    @32
    vi
    cW
    @58
    cY
    wcel
    #
    @58
    vd
    cv
    #
    cfv
    #
    @78
    @69
    cle
    wbr
    #
    @78
    @69
    cif
    #
    cif
    #
    cmpt
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    cfv
    #
    @5
    co
    #
    cmpt
    #
    csumge0
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vw
    @70
    cZ
    cB
    cfv
    cicc
    co
    #
    crab
    #
    cr
    clt
    csup
    #
    @93
    ve
    vf
    vg
    vh
    vj
    vk
    @54
    @68
    vx
    cr
    vd
    @32
    vi
    cW
    @76
    @78
    @78
    vx
    cv
    #
    cle
    wbr
    #
    @78
    @95
    cif
    #
    cif
    #
    cmpt
    #
    cmpt
    #
    cmpt
    #
    cL
    cW
    cX
    cY
    cZ
    va
    vb
    vc
    hoidmvlelem5.l
    wph
    @20
    @47
    @64
    @57
    hoidmvlelem5.f
    ad3antrrr
    wph
    @21
    @47
    @64
    @57
    hoidmvlelem5.y
    ad3antrrr
    wph
    cY
    c0
    wne
    @47
    @64
    @57
    hoidmvlelem5.n
    ad3antrrr
    wph
    cZ
    cX
    cY
    cdif
    wcel
    @47
    @64
    @57
    hoidmvlelem5.z
    ad3antrrr
    hoidmvlelem5.w
    wph
    @23
    @47
    @64
    @57
    hoidmvlelem5.a
    ad3antrrr
    wph
    @24
    @47
    @64
    @57
    hoidmvlelem5.b
    ad3antrrr
    @47
    vk
    cv
    #
    cW
    wcel
    #
    @102
    cA
    cfv
    #
    @102
    cB
    cfv
    #
    clt
    wbr
    #
    wph
    @64
    @57
    @47
    @103
    wa
    @106
    vk
    cW
    wral
    #
    @103
    @106
    @47
    @107
    @103
    @47
    @107
    @46
    @106
    vs
    vk
    cW
    @0
    @102
    wceq
    @2
    @104
    @1
    @105
    clt
    @0
    @102
    cA
    fveq2
    @0
    @102
    cB
    fveq2
    breq12d
    cbvralv
    biimpi
    adantr
    @47
    @103
    simpr
    @106
    vk
    cW
    rspa
    syl2anc
    ad5ant25
    wph
    cn
    @32
    cC
    wf
    @47
    @64
    @57
    hoidmvlelem5.c
    ad3antrrr
    wph
    cn
    @32
    cD
    wf
    @47
    @64
    @57
    hoidmvlelem5.d
    ad3antrrr
    @64
    @48
    @52
    @57
    @48
    @64
    @65
    biimpri
    ad2antlr
    vx
    cr
    @100
    vc
    @32
    vj
    cW
    @7
    cY
    wcel
    #
    @7
    vc
    cv
    #
    cfv
    #
    @110
    @95
    cle
    wbr
    #
    @110
    @95
    cif
    #
    cif
    #
    cmpt
    #
    cmpt
    vd
    vc
    @32
    @99
    @114
    @77
    @109
    wceq
    #
    @99
    vi
    cW
    @76
    @58
    @109
    cfv
    #
    @116
    @95
    cle
    wbr
    #
    @116
    @95
    cif
    #
    cif
    #
    cmpt
    #
    @114
    @115
    vi
    cW
    @98
    @119
    @115
    @76
    @78
    @116
    @97
    @118
    @58
    @77
    @109
    fveq1
    #
    @115
    @96
    @117
    @78
    @116
    @95
    @115
    @78
    @116
    @95
    cle
    @121
    breq1d
    @121
    ifbieq1d
    ifeq12d
    mpteq2dv
    @120
    @114
    wceq
    @115
    vi
    vj
    cW
    @119
    @113
    @58
    @7
    wceq
    #
    @76
    @108
    @116
    @118
    @110
    @112
    @58
    @7
    cY
    eleq1
    @58
    @7
    @109
    fveq2
    #
    @122
    @117
    @111
    @116
    @110
    @95
    @122
    @116
    @110
    @95
    cle
    @123
    breq1d
    @123
    ifbieq1d
    ifbieq12d
    cbvmptv
    a1i
    eqtrd
    cbvmptv
    mpteq2i
    @68
    eqid
    @66
    @57
    simpr
    @91
    @68
    vz
    cv
    #
    @70
    cmin
    co
    #
    cmul
    co
    #
    @55
    vj
    cn
    @8
    @9
    @124
    @101
    cfv
    #
    cfv
    #
    @5
    co
    #
    cmpt
    #
    csumge0
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    vw
    vz
    @92
    @69
    @124
    wceq
    #
    @72
    @126
    @90
    @132
    cle
    @133
    @71
    @125
    @68
    cmul
    @69
    @124
    @70
    cmin
    oveq1
    oveq2d
    @133
    @89
    @131
    @55
    cmul
    @133
    @88
    @130
    csumge0
    @133
    @88
    vl
    cn
    @74
    @75
    @127
    cfv
    #
    @5
    co
    #
    cmpt
    #
    @130
    @133
    vl
    cn
    @87
    @135
    @133
    @86
    @134
    @74
    @5
    @133
    @75
    @85
    @127
    @133
    @69
    @124
    @84
    @101
    @84
    @101
    wceq
    @133
    vw
    vx
    cr
    @83
    @100
    @69
    @95
    wceq
    #
    vd
    @32
    @82
    @99
    @137
    vi
    cW
    @81
    @98
    @137
    @76
    @80
    @97
    @78
    @137
    @79
    @96
    @78
    @69
    @78
    @95
    @69
    @95
    @78
    cle
    breq2
    @137
    @78
    eqidd
    @137
    id
    ifbieq12d
    ifeq2d
    mpteq2dv
    mpteq2dv
    cbvmptv
    a1i
    @133
    id
    fveq12d
    fveq1d
    oveq2d
    mpteq2dv
    @136
    @130
    wceq
    @133
    vl
    vj
    cn
    @135
    @129
    @73
    @7
    wceq
    #
    @74
    @8
    @134
    @128
    @5
    @73
    @7
    cC
    fveq2
    @138
    @75
    @9
    @127
    @73
    @7
    cD
    fveq2
    fveq2d
    oveq12d
    cbvmptv
    a1i
    eqtrd
    fveq2d
    oveq2d
    breq12d
    cbvrabv
    @94
    eqid
    wph
    vk
    cY
    @102
    ve
    cv
    #
    cfv
    @102
    vf
    cv
    #
    cfv
    cico
    co
    cixp
    vj
    cn
    vk
    cY
    @102
    @7
    vg
    cv
    cfv
    #
    cfv
    @102
    @7
    vh
    cv
    cfv
    #
    cfv
    cico
    co
    cixp
    ciun
    wss
    @139
    @140
    @67
    co
    vj
    cn
    @141
    @142
    @67
    co
    cmpt
    csumge0
    cfv
    cle
    wbr
    wi
    vh
    cr
    cY
    cmap
    co
    #
    cn
    cmap
    co
    #
    wral
    vg
    @144
    wral
    vf
    @143
    wral
    ve
    @143
    wral
    @47
    @64
    @57
    hoidmvlelem5.i
    ad3antrrr
    wph
    vk
    cW
    @104
    @105
    cico
    co
    cixp
    vj
    cn
    vk
    cW
    @102
    @8
    cfv
    @102
    @9
    cfv
    cico
    co
    cixp
    ciun
    wss
    @47
    @64
    @57
    hoidmvlelem5.s
    ad3antrrr
    hoidmvlelem4
    syl21anc
    ralrimiva
    @53
    vr
    @6
    @12
    @53
    vr
    nfv
    wph
    @39
    @47
    @48
    @41
    ad2antrr
    @53
    cc0
    cpnf
    @12
    cc0
    cxr
    wcel
    @53
    0xr
    a1i
    cpnf
    cxr
    wcel
    @53
    pnfxr
    a1i
    wph
    @42
    @47
    @48
    @43
    ad2antrr
    wph
    @25
    @47
    @48
    @34
    ad2antrr
    @48
    @12
    cpnf
    clt
    wbr
    @52
    @12
    ltpnf
    adantl
    elicod
    xralrple2
    mpbird
    syl21anc
    pm2.61dan
    pm2.61dan
end
