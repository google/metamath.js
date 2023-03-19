include "cfv.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cn.mm"
include "cv.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cmul.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cr.mm"
include "rge0ssre.mm"
include "cfn.mm"
include "wcel.mm"
include "wss.mm"
include "csn.mm"
include "cun.mm"
include "eldifad.mm"
include "snssi.mm"
include "syl.mm"
include "unssd.mm"
include "syl5eqss.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "hoidmvcl.mm"
include "sseldi.mm"
include "1red.mm"
include "rpred.mm"
include "readdcld.mm"
include "cicc.mm"
include "wne.mm"
include "cvv.mm"
include "nfv.mm"
include "nnex.mm"
include "a1i.mm"
include "wa.mm"
include "icossicc.mm"
include "adantr.mm"
include "cmap.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "breq1d.mm"
include "ifbieq1d.mm"
include "ifbieq12d.mm"
include "cbvmptv.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "cdif.mm"
include "snidg.mm"
include "elun2.mm"
include "eqcomd.mm"
include "eleqtrd.mm"
include "ffvelrnd.mm"
include "hsphoif.mm"
include "sge0clmpt.mm"
include "sge0xrclmpt.mm"
include "cxr.mm"
include "pnfxr.mm"
include "rexrd.mm"
include "eldifbd.mm"
include "eldifd.mm"
include "hsphoidmvle.mm"
include "sge0lempt.mm"
include "ltpnfd.mm"
include "xrlelttrd.mm"
include "xrltned.mm"
include "ge0xrre.mm"
include "remulcld.mm"
include "cmin.mm"
include "crab.mm"
include "clt.mm"
include "ancli.mm"
include "wi.mm"
include "anbi2d.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "sylc.mm"
include "hoidmvlelem1.mm"
include "iccssxr.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "wrex.mm"
include "wn.mm"
include "simpl.mm"
include "simpr.mm"
include "iccssred.mm"
include "sseldd.mm"
include "ltnled.mm"
include "mpbird.mm"
include "cres.mm"
include "cixp.mm"
include "adantlr.mm"
include "eqid.mm"
include "fveq1d.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "reseq1d.mm"
include "crp.mm"
include "biid.mm"
include "eqidd.mm"
include "ifbieq2i.mm"
include "id.mm"
include "fveq12d.mm"
include "ciun.mm"
include "wral.mm"
include "cbvixpv.mm"
include "mpteq12i.mm"
include "hoidmvlelem3.mm"
include "csup.mm"
include "c0.mm"
include "sstrd.mm"
include "ne0i.mm"
include "adantl.mm"
include "sselda.mm"
include "iccleub.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "suprub.mm"
include "syl31anc.mm"
include "syl6breqr.mm"
include "lenltd.mm"
include "ralbidva.mm"
include "mpbid.mm"
include "ralnex.mm"
include "sylib.mm"
include "condan.mm"
include "xrletrid.mm"
include "eqcomi.mm"
include "eleq12d.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "mpteq2dv.mm"
include "fveq2d.mm"
include "elrab.mm"
include "simprd.mm"
include "cvol.mm"
include "cprod.mm"
include "ssfid.mm"
include "hoiprodp1.mm"
include "ssun1.mm"
include "sseqtri.mm"
include "syldan.mm"
include "volicon0.mm"
include "prodeq2dv.mm"
include "fssresd.mm"
include "hoidmvn0val.mm"
include "fvres.mm"
include "volico.mm"
include "eqtr3d.mm"
include "3eqtrd.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"
include "0le1.mm"
include "rpge0d.mm"
include "addge0d.mm"
include "lemul2ad.mm"
include "letrd.mm"

theorem hoidmvlelem4
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cU: class U
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vj: setvar j
  let vk: setvar k
  let cE: class E
  let cG: class G
  let cH: class H
  let cL: class L
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vy: setvar y
  let vu: setvar u
  let vi: setvar i
  let vl: setvar l
  let vw: setvar w
  assume hoidmvlelem4.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume hoidmvlelem4.x: |- ( ph -> X e. Fin )
  assume hoidmvlelem4.y: |- ( ph -> Y C_ X )
  assume hoidmvlelem4.n: |- ( ph -> Y =/= (/) )
  assume hoidmvlelem4.z: |- ( ph -> Z e. ( X \ Y ) )
  assume hoidmvlelem4.w: |- W = ( Y u. { Z } )
  assume hoidmvlelem4.a: |- ( ph -> A : W --> RR )
  assume hoidmvlelem4.b: |- ( ph -> B : W --> RR )
  assume hoidmvlelem4.k: |- ( ( ph /\ k e. W ) -> ( A ` k ) < ( B ` k ) )
  assume hoidmvlelem4.c: |- ( ph -> C : NN --> ( RR ^m W ) )
  assume hoidmvlelem4.d: |- ( ph -> D : NN --> ( RR ^m W ) )
  assume hoidmvlelem4.r: |- ( ph -> ( sum^ ` ( j e. NN |-> ( ( C ` j ) ( L ` W ) ( D ` j ) ) ) ) e. RR )
  assume hoidmvlelem4.h: |- H = ( x e. RR |-> ( c e. ( RR ^m W ) |-> ( j e. W |-> if ( j e. Y , ( c ` j ) , if ( ( c ` j ) <_ x , ( c ` j ) , x ) ) ) ) )
  assume hoidmvlelem4.14: |- G = ( ( A |` Y ) ( L ` Y ) ( B |` Y ) )
  assume hoidmvlelem4.e: |- ( ph -> E e. RR+ )
  assume hoidmvlelem4.u: |- U = { z e. ( ( A ` Z ) [,] ( B ` Z ) ) | ( G x. ( z - ( A ` Z ) ) ) <_ ( ( 1 + E ) x. ( sum^ ` ( j e. NN |-> ( ( C ` j ) ( L ` W ) ( ( H ` z ) ` ( D ` j ) ) ) ) ) ) }
  assume hoidmvlelem4.s: |- S = sup ( U , RR , < )
  assume hoidmvlelem4.i: |- ( ph -> A. e e. ( RR ^m Y ) A. f e. ( RR ^m Y ) A. g e. ( ( RR ^m Y ) ^m NN ) A. h e. ( ( RR ^m Y ) ^m NN ) ( X_ k e. Y ( ( e ` k ) [,) ( f ` k ) ) C_ U_ j e. NN X_ k e. Y ( ( ( g ` j ) ` k ) [,) ( ( h ` j ) ` k ) ) -> ( e ( L ` Y ) f ) <_ ( sum^ ` ( j e. NN |-> ( ( g ` j ) ( L ` Y ) ( h ` j ) ) ) ) ) )
  assume hoidmvlelem4.i2: |- ( ph -> X_ k e. W ( ( A ` k ) [,) ( B ` k ) ) C_ U_ j e. NN X_ k e. W ( ( ( C ` j ) ` k ) [,) ( ( D ` j ) ` k ) ) )

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
  disjoint A c
  disjoint c h
  disjoint c j
  disjoint c k
  disjoint c x
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
  disjoint A z
  disjoint h z
  disjoint j z
  disjoint B a
  disjoint B b
  disjoint B h
  disjoint B j
  disjoint B k
  disjoint B x
  disjoint B c
  disjoint B f
  disjoint B g
  disjoint B z
  disjoint C a
  disjoint C b
  disjoint C h
  disjoint C j
  disjoint C k
  disjoint C x
  disjoint C c
  disjoint C g
  disjoint C z
  disjoint D a
  disjoint D b
  disjoint D h
  disjoint D j
  disjoint D k
  disjoint D x
  disjoint D c
  disjoint D g
  disjoint D z
  disjoint E a
  disjoint E b
  disjoint E h
  disjoint E k
  disjoint E x
  disjoint E c
  disjoint E z
  disjoint G a
  disjoint G b
  disjoint G h
  disjoint G k
  disjoint G x
  disjoint G c
  disjoint G z
  disjoint H a
  disjoint H b
  disjoint H j
  disjoint H k
  disjoint H c
  disjoint H z
  disjoint L a
  disjoint L b
  disjoint L h
  disjoint L j
  disjoint L k
  disjoint L x
  disjoint L c
  disjoint L e
  disjoint L f
  disjoint L g
  disjoint L z
  disjoint S a
  disjoint S b
  disjoint S h
  disjoint S j
  disjoint S k
  disjoint S x
  disjoint S c
  disjoint S g
  disjoint S z
  disjoint U a
  disjoint U b
  disjoint U j
  disjoint U k
  disjoint U x
  disjoint U c
  disjoint U z
  disjoint W a
  disjoint W b
  disjoint W h
  disjoint W j
  disjoint W k
  disjoint W x
  disjoint W c
  disjoint W z
  disjoint Y a
  disjoint Y b
  disjoint Y h
  disjoint Y j
  disjoint Y k
  disjoint Y x
  disjoint Y c
  disjoint Y e
  disjoint Y f
  disjoint Y g
  disjoint Z a
  disjoint Z b
  disjoint Z h
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint Z c
  disjoint Z g
  disjoint Z z
  disjoint a ph
  disjoint b ph
  disjoint h ph
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint c ph
  disjoint k x
  disjoint A y
  disjoint a y
  disjoint b y
  disjoint h y
  disjoint j y
  disjoint k y
  disjoint x y
  disjoint B y
  disjoint B u
  disjoint h u
  disjoint j u
  disjoint u y
  disjoint C i
  disjoint C l
  disjoint C y
  disjoint a i
  disjoint a l
  disjoint b i
  disjoint b l
  disjoint h i
  disjoint h l
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint j l
  disjoint k l
  disjoint l x
  disjoint l y
  disjoint c i
  disjoint c l
  disjoint g i
  disjoint g y
  disjoint C u
  disjoint D i
  disjoint D l
  disjoint D y
  disjoint D u
  disjoint E y
  disjoint G y
  disjoint L l
  disjoint L y
  disjoint S i
  disjoint S l
  disjoint S y
  disjoint S u
  disjoint U y
  disjoint U u
  disjoint W y
  disjoint Y i
  disjoint Y l
  disjoint Y y
  disjoint Y w
  disjoint a w
  disjoint b w
  disjoint h w
  disjoint j w
  disjoint k w
  disjoint w x
  disjoint w y
  disjoint Z i
  disjoint Z l
  disjoint Z y
  disjoint Z u
  disjoint ph y
  disjoint c w
  disjoint ph u
  assert |- ( ph -> ( A ( L ` W ) B ) <_ ( ( 1 + E ) x. ( sum^ ` ( j e. NN |-> ( ( C ` j ) ( L ` W ) ( D ` j ) ) ) ) ) )

  proof
    wph
    cA
    cB
    cW
    cL
    cfv
    #
    co
    #
    c1
    cE
    caddc
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
    @3
    cD
    cfv
    #
    cZ
    cB
    cfv
    #
    cH
    cfv
    #
    cfv
    #
    @0
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
    @2
    vj
    cn
    @4
    @5
    @0
    co
    #
    cmpt
    csumge0
    cfv
    #
    cmul
    co
    wph
    cc0
    cpnf
    cico
    co
    #
    cr
    @1
    rge0ssre
    wph
    vx
    cA
    cB
    vk
    cL
    cW
    va
    vb
    hoidmvlelem4.l
    wph
    cX
    cfn
    wcel
    #
    cW
    cX
    wss
    cW
    cfn
    wcel
    #
    hoidmvlelem4.x
    wph
    cW
    cY
    cZ
    csn
    #
    cun
    #
    cX
    hoidmvlelem4.w
    wph
    cY
    @18
    cX
    hoidmvlelem4.y
    wph
    cZ
    cX
    wcel
    @18
    cX
    wss
    wph
    cZ
    cX
    cY
    hoidmvlelem4.z
    eldifad
    cZ
    cX
    snssi
    syl
    unssd
    syl5eqss
    cX
    cW
    ssfi
    syl2anc
    #
    hoidmvlelem4.a
    hoidmvlelem4.b
    hoidmvcl
    sseldi
    wph
    @2
    @11
    wph
    c1
    cE
    wph
    1red
    #
    wph
    cE
    hoidmvlelem4.e
    rpred
    #
    readdcld
    #
    wph
    @11
    cc0
    cpnf
    cicc
    co
    #
    wcel
    @11
    cpnf
    wne
    @11
    cr
    wcel
    wph
    vj
    cn
    @9
    cvv
    wph
    vj
    nfv
    #
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    #
    wph
    @3
    cn
    wcel
    #
    wa
    #
    @15
    @24
    @9
    cc0
    cpnf
    icossicc
    #
    @28
    vx
    @4
    @8
    vk
    cL
    cW
    va
    vb
    hoidmvlelem4.l
    wph
    @17
    @27
    @20
    adantr
    #
    @28
    @4
    cr
    cW
    cmap
    co
    #
    wcel
    cW
    cr
    @4
    wf
    wph
    cn
    @31
    @3
    cC
    hoidmvlelem4.c
    ffvelrnda
    @4
    cr
    cW
    elmapi
    syl
    #
    @28
    vx
    @6
    @5
    vh
    cH
    cfn
    cW
    cY
    vc
    cH
    vx
    cr
    vc
    @31
    vj
    cW
    @3
    cY
    wcel
    #
    @3
    vc
    cv
    #
    cfv
    #
    @35
    vx
    cv
    #
    cle
    wbr
    #
    @35
    @36
    cif
    #
    cif
    #
    cmpt
    #
    cmpt
    #
    cmpt
    vx
    cr
    vc
    @31
    vh
    cW
    vh
    cv
    #
    cY
    wcel
    #
    @42
    @34
    cfv
    #
    @44
    @36
    cle
    wbr
    #
    @44
    @36
    cif
    #
    cif
    #
    cmpt
    #
    cmpt
    #
    cmpt
    hoidmvlelem4.h
    vx
    cr
    @41
    @49
    vc
    @31
    @40
    @48
    vj
    vh
    cW
    @39
    @47
    @3
    @42
    wceq
    #
    @33
    @43
    @35
    @38
    @44
    @46
    @3
    @42
    cY
    eleq1
    @3
    @42
    @34
    fveq2
    #
    @50
    @37
    @45
    @35
    @44
    @36
    @50
    @35
    @44
    @36
    cle
    @51
    breq1d
    @51
    ifbieq1d
    ifbieq12d
    cbvmptv
    mpteq2i
    mpteq2i
    eqtri
    #
    wph
    @6
    cr
    wcel
    #
    @27
    wph
    cW
    cr
    cZ
    cB
    hoidmvlelem4.b
    wph
    cZ
    @19
    cW
    wph
    cZ
    @18
    wcel
    #
    cZ
    @19
    wcel
    wph
    cZ
    cX
    cY
    cdif
    #
    wcel
    #
    @54
    hoidmvlelem4.z
    cZ
    @55
    snidg
    syl
    cZ
    @18
    cY
    elun2
    syl
    wph
    cW
    @19
    cW
    @19
    wceq
    wph
    hoidmvlelem4.w
    a1i
    eqcomd
    eleqtrd
    #
    ffvelrnd
    #
    adantr
    #
    @30
    @28
    @5
    @31
    wcel
    cW
    cr
    @5
    wf
    wph
    cn
    @31
    @3
    cD
    hoidmvlelem4.d
    ffvelrnda
    @5
    cr
    cW
    elmapi
    syl
    #
    hsphoif
    hoidmvcl
    sseldi
    #
    sge0clmpt
    wph
    @11
    cpnf
    wph
    vj
    cn
    @9
    cvv
    @25
    @26
    @61
    sge0xrclmpt
    #
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    #
    wph
    @11
    @14
    cpnf
    @62
    wph
    @14
    hoidmvlelem4.r
    rexrd
    @63
    wph
    vj
    cn
    @9
    @13
    cvv
    @25
    @26
    @61
    @28
    @15
    @24
    @13
    @29
    @28
    vx
    @4
    @5
    vk
    cL
    cW
    va
    vb
    hoidmvlelem4.l
    @30
    @32
    @60
    hoidmvcl
    sseldi
    @28
    vx
    @4
    @5
    @6
    vh
    vk
    cH
    cL
    cW
    cY
    cZ
    va
    vb
    vc
    hoidmvlelem4.l
    @30
    wph
    cZ
    cW
    cY
    cdif
    wcel
    @27
    wph
    cZ
    cW
    cY
    @57
    wph
    cZ
    cX
    cY
    hoidmvlelem4.z
    eldifbd
    #
    eldifd
    adantr
    hoidmvlelem4.w
    @59
    @52
    @32
    @60
    hsphoidmvle
    sge0lempt
    #
    wph
    @14
    hoidmvlelem4.r
    ltpnfd
    xrlelttrd
    xrltned
    @11
    ge0xrre
    syl2anc
    #
    remulcld
    wph
    @2
    @14
    @23
    hoidmvlelem4.r
    remulcld
    wph
    @1
    @12
    cle
    wbr
    cG
    @6
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
    @12
    cle
    wbr
    #
    wph
    @6
    @67
    @6
    cicc
    co
    #
    wcel
    #
    @70
    wph
    @6
    cG
    vz
    cv
    #
    @67
    cmin
    co
    #
    cmul
    co
    #
    @2
    vj
    cn
    @4
    @5
    @73
    cH
    cfv
    #
    cfv
    #
    @0
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
    vz
    @71
    crab
    #
    wcel
    #
    @72
    @70
    wa
    wph
    @84
    cS
    cU
    wcel
    #
    wph
    vx
    vz
    cA
    cB
    cC
    cD
    cS
    cU
    vj
    vk
    cE
    cG
    cH
    cL
    cW
    cX
    cY
    cZ
    va
    vb
    vc
    hoidmvlelem4.l
    hoidmvlelem4.x
    hoidmvlelem4.y
    hoidmvlelem4.z
    hoidmvlelem4.w
    hoidmvlelem4.a
    hoidmvlelem4.b
    hoidmvlelem4.c
    hoidmvlelem4.d
    hoidmvlelem4.r
    hoidmvlelem4.h
    hoidmvlelem4.14
    hoidmvlelem4.e
    hoidmvlelem4.u
    hoidmvlelem4.s
    wph
    cZ
    cW
    wcel
    #
    wph
    @86
    wa
    #
    @67
    @6
    clt
    wbr
    #
    @57
    wph
    @86
    @57
    ancli
    wph
    vk
    cv
    #
    cW
    wcel
    #
    wa
    #
    @89
    cA
    cfv
    #
    @89
    cB
    cfv
    #
    clt
    wbr
    #
    wi
    @87
    @88
    wi
    vk
    cZ
    cW
    @89
    cZ
    wceq
    #
    @91
    @87
    @94
    @88
    @95
    @90
    @86
    wph
    @89
    cZ
    cW
    eleq1
    anbi2d
    @95
    @92
    @67
    @93
    @6
    clt
    @89
    cZ
    cA
    fveq2
    @89
    cZ
    cB
    fveq2
    breq12d
    imbi12d
    hoidmvlelem4.k
    vtoclg
    sylc
    #
    hoidmvlelem1
    #
    wph
    @6
    cS
    @83
    cU
    wph
    @6
    cS
    wph
    @6
    @58
    rexrd
    #
    wph
    @71
    cxr
    cS
    @67
    @6
    iccssxr
    wph
    cU
    @71
    cS
    cU
    @83
    @71
    hoidmvlelem4.u
    @82
    vz
    @71
    ssrab2
    eqsstri
    #
    @97
    sseldi
    #
    sseldi
    wph
    @6
    cS
    cle
    wbr
    #
    cS
    vu
    cv
    #
    clt
    wbr
    #
    vu
    cU
    wrex
    #
    wph
    @101
    wn
    #
    wa
    #
    wph
    cS
    @6
    clt
    wbr
    #
    @104
    wph
    @105
    simpl
    #
    @106
    @107
    @105
    wph
    @105
    simpr
    @106
    cS
    @6
    wph
    cS
    cr
    wcel
    #
    @105
    wph
    @71
    cr
    cS
    wph
    @67
    @6
    wph
    cW
    cr
    cZ
    cA
    hoidmvlelem4.a
    @57
    ffvelrnd
    #
    @58
    iccssred
    #
    @100
    sseldd
    #
    adantr
    @106
    wph
    @53
    @108
    @58
    syl
    ltnled
    mpbird
    #
    wph
    @107
    wa
    vx
    vy
    vz
    vu
    cA
    cB
    cC
    cD
    vl
    cn
    vl
    cv
    #
    vi
    cn
    cS
    cZ
    vi
    cv
    #
    cC
    cfv
    #
    cfv
    #
    cZ
    @115
    cD
    cfv
    #
    cfv
    #
    cico
    co
    #
    wcel
    #
    @116
    cY
    cres
    #
    vw
    cY
    cc0
    cmpt
    #
    cif
    #
    cmpt
    #
    cfv
    #
    @114
    vi
    cn
    @121
    @118
    cY
    cres
    #
    @123
    cif
    #
    cmpt
    #
    cfv
    #
    cY
    cL
    cfv
    #
    co
    #
    cmpt
    cS
    cU
    ve
    vf
    vg
    vh
    vj
    vk
    cE
    vy
    cY
    cc0
    cmpt
    #
    cG
    cH
    vi
    cn
    @121
    @122
    @133
    cif
    #
    cmpt
    #
    vi
    cn
    @121
    @127
    @133
    cif
    #
    cmpt
    #
    cL
    vx
    vy
    cY
    vy
    cv
    #
    cA
    cfv
    #
    @138
    cB
    cfv
    #
    cico
    co
    #
    cixp
    #
    vy
    cW
    @138
    cY
    wcel
    #
    @138
    @36
    cfv
    #
    cS
    cif
    #
    cmpt
    #
    cmpt
    #
    cW
    cX
    cY
    cZ
    va
    vb
    vc
    hoidmvlelem4.l
    wph
    @16
    @107
    hoidmvlelem4.x
    adantr
    wph
    cY
    cX
    wss
    @107
    hoidmvlelem4.y
    adantr
    wph
    @56
    @107
    hoidmvlelem4.z
    adantr
    hoidmvlelem4.w
    wph
    cW
    cr
    cA
    wf
    #
    @107
    hoidmvlelem4.a
    adantr
    wph
    cW
    cr
    cB
    wf
    #
    @107
    hoidmvlelem4.b
    adantr
    wph
    @90
    @94
    @107
    hoidmvlelem4.k
    adantlr
    @133
    eqid
    wph
    cn
    @31
    cC
    wf
    @107
    hoidmvlelem4.c
    adantr
    vi
    vj
    cn
    @134
    cS
    cZ
    @4
    cfv
    #
    cZ
    @5
    cfv
    #
    cico
    co
    #
    wcel
    #
    @4
    cY
    cres
    #
    @133
    cif
    @115
    @3
    wceq
    #
    @121
    @153
    @122
    @154
    @133
    @155
    @120
    @152
    cS
    @155
    @117
    @150
    @119
    @151
    cico
    @155
    cZ
    @116
    @4
    @115
    @3
    cC
    fveq2
    #
    fveq1d
    @155
    cZ
    @118
    @5
    @115
    @3
    cD
    fveq2
    #
    fveq1d
    oveq12d
    eleq2d
    #
    @155
    @116
    @4
    cY
    @156
    reseq1d
    ifbieq1d
    cbvmptv
    wph
    cn
    @31
    cD
    wf
    @107
    hoidmvlelem4.d
    adantr
    vi
    vj
    cn
    @136
    @153
    @5
    cY
    cres
    #
    @133
    cif
    @155
    @121
    @153
    @127
    @159
    @133
    @158
    @155
    @118
    @5
    cY
    @157
    reseq1d
    ifbieq1d
    cbvmptv
    wph
    @14
    cr
    wcel
    @107
    hoidmvlelem4.r
    adantr
    hoidmvlelem4.h
    hoidmvlelem4.14
    wph
    cE
    crp
    wcel
    @107
    hoidmvlelem4.e
    adantr
    hoidmvlelem4.u
    wph
    @85
    @107
    @97
    adantr
    wph
    @107
    simpr
    vl
    vj
    cn
    @132
    @3
    @135
    cfv
    #
    @3
    @137
    cfv
    #
    @131
    co
    @114
    @3
    wceq
    #
    @126
    @160
    @130
    @161
    @131
    @162
    @114
    @3
    @125
    @135
    @125
    @135
    wceq
    @162
    vi
    cn
    @124
    @134
    @121
    @121
    @123
    @133
    @122
    @121
    biid
    #
    vw
    vy
    cY
    cc0
    cc0
    vw
    cv
    @138
    wceq
    cc0
    eqidd
    cbvmptv
    #
    ifbieq2i
    mpteq2i
    a1i
    @162
    id
    #
    fveq12d
    @162
    @114
    @3
    @129
    @137
    @129
    @137
    wceq
    @162
    vi
    cn
    @128
    @136
    @121
    @121
    @123
    @133
    @127
    @163
    @164
    ifbieq2i
    mpteq2i
    a1i
    @165
    fveq12d
    oveq12d
    cbvmptv
    wph
    vk
    cY
    @89
    ve
    cv
    #
    cfv
    @89
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
    @89
    @3
    vg
    cv
    cfv
    #
    cfv
    @89
    @3
    @42
    cfv
    #
    cfv
    cico
    co
    cixp
    ciun
    wss
    @166
    @167
    @131
    co
    vj
    cn
    @168
    @169
    @131
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
    @171
    wral
    vf
    @170
    wral
    ve
    @170
    wral
    @107
    hoidmvlelem4.i
    adantr
    wph
    vk
    cW
    @92
    @93
    cico
    co
    #
    cixp
    vj
    cn
    vk
    cW
    @89
    @4
    cfv
    @89
    @5
    cfv
    cico
    co
    cixp
    ciun
    wss
    @107
    hoidmvlelem4.i2
    adantr
    @147
    @147
    vx
    vk
    cY
    @172
    cixp
    #
    vk
    cW
    @89
    cY
    wcel
    #
    @89
    @36
    cfv
    #
    cS
    cif
    #
    cmpt
    #
    cmpt
    @147
    eqid
    vx
    @142
    @146
    @173
    @177
    vy
    vk
    cY
    @141
    @172
    @138
    @89
    wceq
    #
    @139
    @92
    @140
    @93
    cico
    @138
    @89
    cA
    fveq2
    @138
    @89
    cB
    fveq2
    oveq12d
    cbvixpv
    vy
    vk
    cW
    @145
    @176
    @178
    @143
    @174
    @144
    @175
    cS
    @138
    @89
    cY
    eleq1
    @138
    @89
    @36
    fveq2
    ifbieq1d
    cbvmptv
    mpteq12i
    eqtri
    hoidmvlelem3
    syl2anc
    @106
    wph
    @107
    @104
    wn
    #
    @108
    @113
    wph
    @179
    @107
    wph
    @103
    wn
    #
    vu
    cU
    wral
    #
    @179
    wph
    @102
    cS
    cle
    wbr
    #
    vu
    cU
    wral
    @181
    wph
    @182
    vu
    cU
    wph
    @102
    cU
    wcel
    #
    wa
    #
    @102
    cU
    cr
    clt
    csup
    #
    cS
    cle
    @184
    cU
    cr
    wss
    #
    cU
    c0
    wne
    #
    @102
    @138
    cle
    wbr
    #
    vu
    cU
    wral
    #
    vy
    cr
    wrex
    #
    @183
    @102
    @185
    cle
    wbr
    wph
    @186
    @183
    wph
    cU
    @71
    cr
    cU
    @71
    wss
    wph
    @99
    a1i
    #
    @111
    sstrd
    adantr
    #
    @183
    @187
    wph
    cU
    @102
    ne0i
    adantl
    wph
    @190
    @183
    wph
    @53
    @102
    @6
    cle
    wbr
    #
    vu
    cU
    wral
    #
    @190
    @58
    wph
    @193
    vu
    cU
    @184
    @67
    cxr
    wcel
    #
    @6
    cxr
    wcel
    #
    @102
    @71
    wcel
    @193
    wph
    @195
    @183
    wph
    @67
    @110
    rexrd
    #
    adantr
    wph
    @196
    @183
    @98
    adantr
    wph
    cU
    @71
    @102
    @191
    sselda
    @67
    @6
    @102
    iccleub
    syl3anc
    ralrimiva
    @189
    @194
    vy
    @6
    cr
    @138
    @6
    wceq
    @188
    @193
    vu
    cU
    @138
    @6
    @102
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    adantr
    wph
    @183
    simpr
    #
    vy
    vu
    cU
    @102
    suprub
    syl31anc
    hoidmvlelem4.s
    syl6breqr
    ralrimiva
    wph
    @182
    @180
    vu
    cU
    @184
    @102
    cS
    @184
    cU
    cr
    @102
    @192
    @198
    sseldd
    wph
    @109
    @183
    @112
    adantr
    lenltd
    ralbidva
    mpbid
    @103
    vu
    cU
    ralnex
    sylib
    adantr
    syl2anc
    condan
    wph
    @195
    @196
    cS
    @71
    wcel
    cS
    @6
    cle
    wbr
    @197
    @98
    @100
    @67
    @6
    cS
    iccleub
    syl3anc
    xrletrid
    @83
    cU
    wceq
    wph
    cU
    @83
    hoidmvlelem4.u
    eqcomi
    a1i
    eleq12d
    mpbird
    @82
    @70
    vz
    @6
    @71
    @73
    @6
    wceq
    #
    @75
    @69
    @81
    @12
    cle
    @199
    @74
    @68
    cG
    cmul
    @73
    @6
    @67
    cmin
    oveq1
    oveq2d
    @199
    @80
    @11
    @2
    cmul
    @199
    @79
    @10
    csumge0
    @199
    vj
    cn
    @78
    @9
    @199
    @77
    @8
    @4
    @0
    @199
    @5
    @76
    @7
    @73
    @6
    cH
    fveq2
    fveq1d
    oveq2d
    mpteq2dv
    fveq2d
    oveq2d
    breq12d
    elrab
    sylib
    simprd
    wph
    @1
    @69
    @12
    cle
    wph
    @1
    cY
    @172
    cvol
    cfv
    #
    vk
    cprod
    #
    @67
    @6
    cico
    co
    cvol
    cfv
    #
    cmul
    co
    @69
    wph
    vx
    cA
    cB
    vk
    @201
    cL
    @55
    cW
    cY
    cZ
    va
    vb
    hoidmvlelem4.l
    wph
    cX
    cY
    hoidmvlelem4.x
    hoidmvlelem4.y
    ssfid
    #
    hoidmvlelem4.z
    @64
    hoidmvlelem4.w
    hoidmvlelem4.a
    hoidmvlelem4.b
    @201
    eqid
    hoiprodp1
    wph
    @201
    cG
    @202
    @68
    cmul
    wph
    cY
    @93
    @92
    cmin
    co
    #
    vk
    cprod
    #
    @205
    @201
    cG
    wph
    @205
    eqidd
    wph
    cY
    @200
    @204
    vk
    wph
    @174
    wa
    #
    @92
    @93
    @206
    cW
    cr
    @89
    cA
    wph
    @148
    @174
    hoidmvlelem4.a
    adantr
    @206
    cY
    cW
    @89
    cY
    @19
    cW
    cY
    @18
    ssun1
    cW
    @19
    hoidmvlelem4.w
    eqcomi
    sseqtri
    #
    wph
    @174
    simpr
    sseldi
    #
    ffvelrnd
    #
    @206
    cW
    cr
    @89
    cB
    wph
    @149
    @174
    hoidmvlelem4.b
    adantr
    @208
    ffvelrnd
    #
    wph
    @174
    @90
    @94
    @208
    hoidmvlelem4.k
    syldan
    volicon0
    #
    prodeq2dv
    wph
    cG
    cA
    cY
    cres
    #
    cB
    cY
    cres
    #
    @131
    co
    #
    cY
    @89
    @212
    cfv
    #
    @89
    @213
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    @205
    cG
    @214
    wceq
    wph
    hoidmvlelem4.14
    a1i
    wph
    vx
    @212
    @213
    vk
    cL
    cY
    va
    vb
    hoidmvlelem4.l
    @203
    hoidmvlelem4.n
    wph
    cW
    cr
    cY
    cA
    hoidmvlelem4.a
    cY
    cW
    wss
    wph
    @207
    a1i
    #
    fssresd
    wph
    cW
    cr
    cY
    cB
    hoidmvlelem4.b
    @219
    fssresd
    hoidmvn0val
    wph
    cY
    @218
    @204
    vk
    @206
    @218
    @200
    @94
    @204
    cc0
    cif
    #
    @204
    @174
    @218
    @200
    wceq
    wph
    @174
    @217
    @172
    cvol
    @174
    @215
    @92
    @216
    @93
    cico
    @89
    cY
    cA
    fvres
    @89
    cY
    cB
    fvres
    oveq12d
    fveq2d
    adantl
    @206
    @92
    cr
    wcel
    @93
    cr
    wcel
    @200
    @220
    wceq
    @209
    @210
    @92
    @93
    volico
    syl2anc
    #
    @206
    @200
    @220
    @204
    @221
    @211
    eqtr3d
    3eqtrd
    prodeq2dv
    3eqtrd
    3eqtr4d
    wph
    @67
    @6
    @110
    @58
    @96
    volicon0
    oveq12d
    eqtrd
    breq1d
    mpbird
    wph
    @11
    @14
    @2
    @66
    hoidmvlelem4.r
    @23
    wph
    c1
    cE
    @21
    @22
    cc0
    c1
    cle
    wbr
    wph
    0le1
    a1i
    wph
    cE
    hoidmvlelem4.e
    rpge0d
    addge0d
    @65
    lemul2ad
    letrd
end
