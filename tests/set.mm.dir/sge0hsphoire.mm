include "cn.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "wcel.mm"
include "wne.mm"
include "cr.mm"
include "cvv.mm"
include "nnex.mm"
include "a1i.mm"
include "cico.mm"
include "wa.mm"
include "cfn.mm"
include "csn.mm"
include "cun.mm"
include "snfi.mm"
include "unfi.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "adantr.mm"
include "cmap.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "syl.mm"
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
include "hsphoif.mm"
include "hoidmvcl.mm"
include "eqid.mm"
include "fmptd.mm"
include "wss.mm"
include "icossicc.mm"
include "fssd.mm"
include "sge0cl.mm"
include "sge0xrcl.mm"
include "cxr.mm"
include "pnfxr.mm"
include "rexrd.mm"
include "nfv.mm"
include "sseldi.mm"
include "cdif.mm"
include "hsphoidmvle.mm"
include "sge0lempt.mm"
include "ltpnfd.mm"
include "xrlelttrd.mm"
include "xrltned.mm"
include "ge0xrre.mm"

theorem sge0hsphoire
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let cH: class H
  let cL: class L
  let cW: class W
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vh: setvar h
  assume sge0hsphoire.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume sge0hsphoire.f: |- ( ph -> Y e. Fin )
  assume sge0hsphoire.z: |- ( ph -> Z e. ( W \ Y ) )
  assume sge0hsphoire.w: |- W = ( Y u. { Z } )
  assume sge0hsphoire.c: |- ( ph -> C : NN --> ( RR ^m W ) )
  assume sge0hsphoire.d: |- ( ph -> D : NN --> ( RR ^m W ) )
  assume sge0hsphoire.r: |- ( ph -> ( sum^ ` ( j e. NN |-> ( ( C ` j ) ( L ` W ) ( D ` j ) ) ) ) e. RR )
  assume sge0hsphoire.h: |- H = ( x e. RR |-> ( c e. ( RR ^m W ) |-> ( j e. W |-> if ( j e. Y , ( c ` j ) , if ( ( c ` j ) <_ x , ( c ` j ) , x ) ) ) ) )
  assume sge0hsphoire.s: |- ( ph -> S e. RR )

  disjoint C a
  disjoint C b
  disjoint C k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint D a
  disjoint D b
  disjoint D k
  disjoint D c
  disjoint c k
  disjoint H a
  disjoint H b
  disjoint H k
  disjoint S a
  disjoint S b
  disjoint S k
  disjoint S x
  disjoint a x
  disjoint b x
  disjoint k x
  disjoint S c
  disjoint c x
  disjoint W a
  disjoint W b
  disjoint W j
  disjoint W k
  disjoint W x
  disjoint a j
  disjoint b j
  disjoint j k
  disjoint j x
  disjoint W c
  disjoint c j
  disjoint Y c
  disjoint Y j
  disjoint Y x
  disjoint Z c
  disjoint Z k
  disjoint Z x
  disjoint a ph
  disjoint b ph
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint c ph
  disjoint k x
  disjoint D h
  disjoint c h
  disjoint h k
  disjoint S h
  disjoint h x
  disjoint W h
  disjoint h j
  disjoint Y h
  disjoint Z h
  disjoint h ph
  assert |- ( ph -> ( sum^ ` ( j e. NN |-> ( ( C ` j ) ( L ` W ) ( ( H ` S ) ` ( D ` j ) ) ) ) ) e. RR )

  proof
    wph
    vj
    cn
    vj
    cv
    #
    cC
    cfv
    #
    @0
    cD
    cfv
    #
    cS
    cH
    cfv
    cfv
    #
    cW
    cL
    cfv
    #
    co
    #
    cmpt
    #
    csumge0
    cfv
    #
    cc0
    cpnf
    cicc
    co
    #
    wcel
    @7
    cpnf
    wne
    @7
    cr
    wcel
    wph
    @6
    cvv
    cn
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    #
    wph
    cn
    cc0
    cpnf
    cico
    co
    #
    @8
    @6
    wph
    vj
    cn
    @5
    @10
    @6
    wph
    @0
    cn
    wcel
    #
    wa
    #
    vx
    @1
    @3
    vk
    cL
    cW
    va
    vb
    sge0hsphoire.l
    wph
    cW
    cfn
    wcel
    @11
    wph
    cW
    cY
    cZ
    csn
    #
    cun
    #
    cfn
    sge0hsphoire.w
    wph
    cY
    cfn
    wcel
    @13
    cfn
    wcel
    #
    @14
    cfn
    wcel
    sge0hsphoire.f
    @15
    wph
    cZ
    snfi
    a1i
    cY
    @13
    unfi
    syl2anc
    syl5eqel
    adantr
    #
    @12
    @1
    cr
    cW
    cmap
    co
    #
    wcel
    cW
    cr
    @1
    wf
    wph
    cn
    @17
    @0
    cC
    sge0hsphoire.c
    ffvelrnda
    @1
    cr
    cW
    elmapi
    syl
    #
    @12
    vx
    cS
    @2
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
    @17
    vj
    cW
    @0
    cY
    wcel
    #
    @0
    vc
    cv
    #
    cfv
    #
    @21
    vx
    cv
    #
    cle
    wbr
    #
    @21
    @22
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
    @17
    vh
    cW
    vh
    cv
    #
    cY
    wcel
    #
    @28
    @20
    cfv
    #
    @30
    @22
    cle
    wbr
    #
    @30
    @22
    cif
    #
    cif
    #
    cmpt
    #
    cmpt
    #
    cmpt
    sge0hsphoire.h
    vx
    cr
    @27
    @35
    vc
    @17
    @26
    @34
    vj
    vh
    cW
    @25
    @33
    @0
    @28
    wceq
    #
    @19
    @29
    @21
    @24
    @30
    @32
    @0
    @28
    cY
    eleq1
    @0
    @28
    @20
    fveq2
    #
    @36
    @23
    @31
    @21
    @30
    @22
    @36
    @21
    @30
    @22
    cle
    @37
    breq1d
    @37
    ifbieq1d
    ifbieq12d
    cbvmptv
    mpteq2i
    mpteq2i
    eqtri
    #
    wph
    cS
    cr
    wcel
    @11
    sge0hsphoire.s
    adantr
    #
    @16
    @12
    @2
    @17
    wcel
    cW
    cr
    @2
    wf
    wph
    cn
    @17
    @0
    cD
    sge0hsphoire.d
    ffvelrnda
    @2
    cr
    cW
    elmapi
    syl
    #
    hsphoif
    hoidmvcl
    #
    @6
    eqid
    fmptd
    @10
    @8
    wss
    wph
    cc0
    cpnf
    icossicc
    #
    a1i
    fssd
    #
    sge0cl
    wph
    @7
    cpnf
    wph
    @6
    cvv
    cn
    @9
    @43
    sge0xrcl
    #
    cpnf
    cxr
    wcel
    wph
    pnfxr
    a1i
    #
    wph
    @7
    vj
    cn
    @1
    @2
    @4
    co
    #
    cmpt
    csumge0
    cfv
    #
    cpnf
    @44
    wph
    @47
    sge0hsphoire.r
    rexrd
    @45
    wph
    vj
    cn
    @5
    @46
    cvv
    wph
    vj
    nfv
    @9
    @12
    @10
    @8
    @5
    @42
    @41
    sseldi
    @12
    @10
    @8
    @46
    @42
    @12
    vx
    @1
    @2
    vk
    cL
    cW
    va
    vb
    sge0hsphoire.l
    @16
    @18
    @40
    hoidmvcl
    sseldi
    @12
    vx
    @1
    @2
    cS
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
    sge0hsphoire.l
    @16
    wph
    cZ
    cW
    cY
    cdif
    wcel
    @11
    sge0hsphoire.z
    adantr
    sge0hsphoire.w
    @39
    @38
    @18
    @40
    hsphoidmvle
    sge0lempt
    wph
    @47
    sge0hsphoire.r
    ltpnfd
    xrlelttrd
    xrltned
    @7
    ge0xrre
    syl2anc
end
