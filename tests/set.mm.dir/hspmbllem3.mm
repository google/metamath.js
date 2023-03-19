include "cfv.mm"
include "co.mm"
include "cin.mm"
include "covoln.mm"
include "cdif.mm"
include "cxad.mm"
include "caddc.mm"
include "cle.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "cmap.mm"
include "inss1.mm"
include "syl5ss.mm"
include "ovncl.mm"
include "wss.mm"
include "a1i.mm"
include "ovnssle.mm"
include "ge0lere.mm"
include "ssdifssd.mm"
include "difssd.mm"
include "rexadd.mm"
include "syl2anc.mm"
include "wbr.mm"
include "cv.mm"
include "crp.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cfn.mm"
include "adantr.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "syl.mm"
include "simpr.mm"
include "ovncvrrp.mm"
include "cif.mm"
include "cmpt.mm"
include "csn.mm"
include "cc0.mm"
include "cico.mm"
include "cvol.mm"
include "cprod.mm"
include "cmpt2.mm"
include "ad2antrr.mm"
include "cn.mm"
include "wf.mm"
include "cixp.mm"
include "ciun.mm"
include "csumge0.mm"
include "cpw.mm"
include "crab.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "mpteq2dv.mm"
include "breq1d.mm"
include "cbvrabv.mm"
include "mpteq2i.mm"
include "eqtri.mm"
include "ovncvr2.mm"
include "simplld.mm"
include "simpld.mm"
include "simprd.mm"
include "simplrd.mm"
include "rpred.mm"
include "rexaddd.mm"
include "breqtrd.mm"
include "eqid.mm"
include "hspmbllem2.mm"
include "ex.mm"
include "exlimdv.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "wb.mm"
include "readdcld.mm"
include "alrple.mm"
include "mpbird.mm"
include "eqbrtrd.mm"

theorem hspmbllem3
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let vh: setvar h
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let cH: class H
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let vr: setvar r
  let va: setvar a
  let vl: setvar l
  let vb: setvar b
  let vc: setvar c
  let ve: setvar e
  assume hspmbllem3.h: |- H = ( x e. Fin |-> ( l e. x , y e. RR |-> X_ k e. x if ( k = l , ( -oo (,) y ) , RR ) ) )
  assume hspmbllem3.x: |- ( ph -> X e. Fin )
  assume hspmbllem3.i: |- ( ph -> K e. X )
  assume hspmbllem3.y: |- ( ph -> Y e. RR )
  assume hspmbllem3.a: |- ( ph -> ( ( voln* ` X ) ` A ) e. RR )
  assume hspmbllem3.s: |- ( ph -> A C_ ( RR ^m X ) )
  assume hspmbllem3.c: |- C = ( a e. ~P ( RR ^m X ) |-> { l e. ( ( ( RR X. RR ) ^m X ) ^m NN ) | a C_ U_ j e. NN X_ k e. X ( ( [,) o. ( l ` j ) ) ` k ) } )
  assume hspmbllem3.l: |- L = ( h e. ( ( RR X. RR ) ^m X ) |-> prod_ k e. X ( vol ` ( ( [,) o. h ) ` k ) ) )
  assume hspmbllem3.d: |- D = ( a e. ~P ( RR ^m X ) |-> ( r e. RR+ |-> { i e. ( C ` a ) | ( sum^ ` ( j e. NN |-> ( L ` ( i ` j ) ) ) ) <_ ( ( ( voln* ` X ) ` a ) +e r ) } ) )
  assume hspmbllem3.10: |- B = ( j e. NN |-> ( k e. X |-> ( 1st ` ( ( i ` j ) ` k ) ) ) )
  assume hspmbllem3.11: |- T = ( j e. NN |-> ( k e. X |-> ( 2nd ` ( ( i ` j ) ` k ) ) ) )

  disjoint A a
  disjoint A h
  disjoint A i
  disjoint A j
  disjoint A k
  disjoint A l
  disjoint A x
  disjoint A y
  disjoint a h
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a l
  disjoint a x
  disjoint a y
  disjoint h i
  disjoint h j
  disjoint h k
  disjoint h l
  disjoint h x
  disjoint h y
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j l
  disjoint j x
  disjoint j y
  disjoint k l
  disjoint k x
  disjoint k y
  disjoint l x
  disjoint l y
  disjoint x y
  disjoint A r
  disjoint a r
  disjoint h r
  disjoint i r
  disjoint j r
  disjoint B a
  disjoint B h
  disjoint B k
  disjoint B l
  disjoint C a
  disjoint C h
  disjoint C i
  disjoint C r
  disjoint D a
  disjoint D h
  disjoint D j
  disjoint D k
  disjoint D l
  disjoint D x
  disjoint D y
  disjoint D r
  disjoint H i
  disjoint H j
  disjoint H k
  disjoint K a
  disjoint K h
  disjoint K i
  disjoint K j
  disjoint K k
  disjoint K l
  disjoint K x
  disjoint K y
  disjoint L a
  disjoint L h
  disjoint L i
  disjoint L r
  disjoint T a
  disjoint T h
  disjoint T j
  disjoint T k
  disjoint T l
  disjoint X a
  disjoint X h
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X l
  disjoint X x
  disjoint X y
  disjoint X r
  disjoint Y a
  disjoint Y h
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint Y l
  disjoint Y x
  disjoint Y y
  disjoint a ph
  disjoint h ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint l ph
  disjoint ph x
  disjoint ph y
  disjoint ph r
  disjoint k x
  disjoint A b
  disjoint A c
  disjoint A e
  disjoint a b
  disjoint a c
  disjoint a e
  disjoint b c
  disjoint b e
  disjoint b h
  disjoint b i
  disjoint b j
  disjoint b k
  disjoint b l
  disjoint b x
  disjoint b y
  disjoint c e
  disjoint c h
  disjoint c i
  disjoint c j
  disjoint c k
  disjoint c l
  disjoint c x
  disjoint c y
  disjoint e h
  disjoint e i
  disjoint e j
  disjoint e k
  disjoint e l
  disjoint e x
  disjoint e y
  disjoint e r
  disjoint B b
  disjoint B c
  disjoint D b
  disjoint D c
  disjoint H e
  disjoint K b
  disjoint K c
  disjoint K e
  disjoint T b
  disjoint T c
  disjoint X b
  disjoint X c
  disjoint X e
  disjoint Y b
  disjoint Y c
  disjoint Y e
  disjoint b ph
  disjoint c ph
  disjoint e ph
  assert |- ( ph -> ( ( ( voln* ` X ) ` ( A i^i ( K ( H ` X ) Y ) ) ) +e ( ( voln* ` X ) ` ( A \ ( K ( H ` X ) Y ) ) ) ) <_ ( ( voln* ` X ) ` A ) )

  proof
    wph
    cA
    cK
    cY
    cX
    cH
    cfv
    co
    #
    cin
    #
    cX
    covoln
    cfv
    #
    cfv
    #
    cA
    @0
    cdif
    #
    @2
    cfv
    #
    cxad
    co
    #
    @3
    @5
    caddc
    co
    #
    cA
    @2
    cfv
    #
    cle
    wph
    @3
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    @6
    @7
    wceq
    wph
    @8
    @3
    hspmbllem3.a
    wph
    @1
    cX
    hspmbllem3.x
    wph
    @1
    cA
    cr
    cX
    cmap
    co
    #
    cA
    @0
    inss1
    #
    hspmbllem3.s
    syl5ss
    ovncl
    wph
    @1
    cA
    cX
    hspmbllem3.x
    @1
    cA
    wss
    wph
    @12
    a1i
    hspmbllem3.s
    ovnssle
    ge0lere
    #
    wph
    @8
    @5
    hspmbllem3.a
    wph
    @4
    cX
    hspmbllem3.x
    wph
    cA
    @11
    @0
    hspmbllem3.s
    ssdifssd
    ovncl
    wph
    @4
    cA
    cX
    hspmbllem3.x
    wph
    cA
    @0
    difssd
    hspmbllem3.s
    ovnssle
    ge0lere
    #
    @3
    @5
    rexadd
    syl2anc
    wph
    @7
    @8
    cle
    wbr
    #
    @7
    @8
    ve
    cv
    #
    caddc
    co
    #
    cle
    wbr
    #
    ve
    crp
    wral
    #
    wph
    @18
    ve
    crp
    wph
    @16
    crp
    wcel
    #
    wa
    #
    vi
    cv
    #
    @16
    cA
    cD
    cfv
    cfv
    wcel
    #
    vi
    wex
    @18
    @21
    cA
    cC
    cD
    vr
    vh
    vi
    vj
    vk
    @16
    cL
    cX
    va
    vl
    wph
    cX
    cfn
    wcel
    #
    @20
    hspmbllem3.x
    adantr
    #
    wph
    cX
    c0
    wne
    #
    @20
    wph
    cK
    cX
    wcel
    #
    @26
    hspmbllem3.i
    cX
    cK
    ne0i
    syl
    adantr
    wph
    cA
    @11
    wss
    #
    @20
    hspmbllem3.s
    adantr
    #
    wph
    @20
    simpr
    #
    hspmbllem3.c
    hspmbllem3.l
    hspmbllem3.d
    ovncvrrp
    @21
    @23
    @18
    vi
    @21
    @23
    @18
    @21
    @23
    wa
    #
    vx
    vy
    cA
    cB
    cT
    vx
    cr
    vc
    @11
    vh
    cX
    vh
    cv
    #
    cK
    wceq
    vx
    cv
    #
    @32
    vc
    cv
    cfv
    #
    cle
    wbr
    @34
    @33
    cif
    @34
    cif
    cmpt
    cmpt
    cmpt
    #
    vy
    cr
    vc
    @11
    vh
    cX
    @32
    cX
    cK
    csn
    cdif
    wcel
    @34
    @34
    vy
    cv
    #
    cle
    wbr
    @34
    @36
    cif
    cif
    cmpt
    cmpt
    cmpt
    #
    vh
    vj
    vk
    @16
    cH
    cK
    vx
    cfn
    va
    vb
    cr
    @33
    cmap
    co
    #
    @38
    @33
    c0
    wceq
    cc0
    @33
    vk
    cv
    #
    va
    cv
    #
    cfv
    @39
    vb
    cv
    cfv
    cico
    co
    cvol
    cfv
    vk
    cprod
    cif
    cmpt2
    cmpt
    #
    cX
    cY
    va
    vb
    vc
    vl
    hspmbllem3.h
    @21
    @24
    @23
    @25
    adantr
    #
    wph
    @27
    @20
    @23
    hspmbllem3.i
    ad2antrr
    wph
    cY
    cr
    wcel
    @20
    @23
    hspmbllem3.y
    ad2antrr
    @21
    @20
    @23
    @30
    adantr
    #
    @31
    cn
    @11
    cB
    wf
    #
    cn
    @11
    cT
    wf
    #
    @31
    @44
    @45
    wa
    #
    cA
    vj
    cn
    vk
    cX
    @39
    vj
    cv
    #
    cB
    cfv
    cfv
    @39
    @47
    cT
    cfv
    cfv
    cico
    co
    #
    cixp
    ciun
    wss
    #
    vj
    cn
    cX
    @48
    cvol
    cfv
    vk
    cprod
    cmpt
    csumge0
    cfv
    #
    @8
    @16
    cxad
    co
    #
    cle
    wbr
    #
    @31
    cA
    cB
    cC
    cD
    cT
    vh
    vh
    vj
    vk
    @16
    @22
    cL
    cX
    vr
    va
    vl
    @42
    @21
    @28
    @23
    @29
    adantr
    @43
    hspmbllem3.c
    hspmbllem3.l
    cD
    va
    @11
    cpw
    #
    vr
    crp
    vj
    cn
    @47
    @22
    cfv
    #
    cL
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @40
    @2
    cfv
    vr
    cv
    cxad
    co
    #
    cle
    wbr
    #
    vi
    @40
    cC
    cfv
    #
    crab
    #
    cmpt
    #
    cmpt
    va
    @53
    vr
    crp
    vj
    cn
    @47
    @32
    cfv
    #
    cL
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    #
    @58
    cle
    wbr
    #
    vh
    @60
    crab
    #
    cmpt
    #
    cmpt
    hspmbllem3.d
    va
    @53
    @62
    @69
    vr
    crp
    @61
    @68
    @59
    @67
    vi
    vh
    @60
    @22
    @32
    wceq
    #
    @57
    @66
    @58
    cle
    @70
    @56
    @65
    csumge0
    @70
    vj
    cn
    @55
    @64
    @70
    @54
    @63
    cL
    @47
    @22
    @32
    fveq1
    fveq2d
    mpteq2dv
    fveq2d
    breq1d
    cbvrabv
    mpteq2i
    mpteq2i
    eqtri
    @21
    @23
    simpr
    hspmbllem3.10
    hspmbllem3.11
    ovncvr2
    #
    simplld
    #
    simpld
    @31
    @44
    @45
    @72
    simprd
    @31
    @46
    @49
    @52
    @71
    simplrd
    @31
    @50
    @51
    @17
    cle
    @31
    @46
    @49
    wa
    @52
    @71
    simprd
    @21
    @51
    @17
    wceq
    @23
    @21
    @8
    @16
    wph
    @8
    cr
    wcel
    #
    @20
    hspmbllem3.a
    adantr
    @21
    @16
    @30
    rpred
    rexaddd
    adantr
    breqtrd
    wph
    @73
    @20
    @23
    hspmbllem3.a
    ad2antrr
    wph
    @9
    @20
    @23
    @13
    ad2antrr
    wph
    @10
    @20
    @23
    @14
    ad2antrr
    @41
    eqid
    @37
    eqid
    @35
    eqid
    hspmbllem2
    ex
    exlimdv
    mpd
    ralrimiva
    wph
    @7
    cr
    wcel
    @73
    @15
    @19
    wb
    wph
    @3
    @5
    @13
    @14
    readdcld
    hspmbllem3.a
    ve
    @7
    @8
    alrple
    syl2anc
    mpbird
    eqbrtrd
end
