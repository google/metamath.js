include "cfv.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cico.mm"
include "cvol.mm"
include "cprod.mm"
include "nfv.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "cfn.mm"
include "hoidifhspf.mm"
include "ffvelrnda.mm"
include "volicore.mm"
include "syl2anc.mm"
include "cdm.mm"
include "cc0.mm"
include "cxr.mm"
include "rexrd.mm"
include "icombl.mm"
include "volge0.mm"
include "syl.mm"
include "wss.mm"
include "wceq.mm"
include "cif.mm"
include "adantr.mm"
include "max2.mm"
include "wf.mm"
include "simpr.mm"
include "hoidifhspval3.mm"
include "iftrue.mm"
include "adantl.mm"
include "eqtr2d.mm"
include "breqtrd.mm"
include "wn.mm"
include "leidd.mm"
include "iffalse.mm"
include "pm2.61dan.mm"
include "icossico.mm"
include "syl22anc.mm"
include "volss.mm"
include "syl3anc.mm"
include "fprodle.mm"
include "c0.mm"
include "wne.mm"
include "ne0i.mm"
include "hoidmvn0val.mm"
include "breq12d.mm"
include "mpbird.mm"

theorem hoidifhspdmvle
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let vh: setvar h
  let vk: setvar k
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume hoidifhspdmvle.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume hoidifhspdmvle.x: |- ( ph -> X e. Fin )
  assume hoidifhspdmvle.a: |- ( ph -> A : X --> RR )
  assume hoidifhspdmvle.b: |- ( ph -> B : X --> RR )
  assume hoidifhspdmvle.k: |- ( ph -> K e. X )
  assume hoidifhspdmvle.d: |- D = ( x e. RR |-> ( c e. ( RR ^m X ) |-> ( h e. X |-> if ( h = K , if ( x <_ ( c ` h ) , ( c ` h ) , x ) , ( c ` h ) ) ) ) )
  assume hoidifhspdmvle.y: |- ( ph -> Y e. RR )

  disjoint A a
  disjoint A b
  disjoint A k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint A c
  disjoint A h
  disjoint c h
  disjoint c k
  disjoint h k
  disjoint B a
  disjoint B b
  disjoint B k
  disjoint D a
  disjoint D b
  disjoint D k
  disjoint K c
  disjoint K h
  disjoint K x
  disjoint c x
  disjoint h x
  disjoint X a
  disjoint X b
  disjoint X k
  disjoint X x
  disjoint a x
  disjoint b x
  disjoint k x
  disjoint X c
  disjoint X h
  disjoint Y a
  disjoint Y b
  disjoint Y k
  disjoint Y x
  disjoint Y c
  disjoint Y h
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint ph x
  disjoint c ph
  disjoint h ph
  disjoint k x
  assert |- ( ph -> ( ( ( D ` Y ) ` A ) ( L ` X ) B ) <_ ( A ( L ` X ) B ) )

  proof
    wph
    cA
    cY
    cD
    cfv
    cfv
    #
    cB
    cX
    cL
    cfv
    #
    co
    #
    cA
    cB
    @1
    co
    #
    cle
    wbr
    cX
    vk
    cv
    #
    @0
    cfv
    #
    @4
    cB
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
    #
    cX
    @4
    cA
    cfv
    #
    @6
    cico
    co
    #
    cvol
    cfv
    #
    vk
    cprod
    #
    cle
    wbr
    wph
    cX
    @8
    @12
    vk
    wph
    vk
    nfv
    hoidifhspdmvle.x
    wph
    @4
    cX
    wcel
    #
    wa
    #
    @5
    cr
    wcel
    #
    @6
    cr
    wcel
    #
    @8
    cr
    wcel
    wph
    cX
    cr
    @4
    @0
    wph
    vx
    cA
    cD
    vh
    cK
    cfn
    cX
    cY
    vc
    hoidifhspdmvle.d
    hoidifhspdmvle.y
    hoidifhspdmvle.x
    hoidifhspdmvle.a
    hoidifhspf
    #
    ffvelrnda
    #
    wph
    cX
    cr
    @4
    cB
    hoidifhspdmvle.b
    ffvelrnda
    #
    @5
    @6
    volicore
    syl2anc
    @15
    @7
    cvol
    cdm
    #
    wcel
    #
    cc0
    @8
    cle
    wbr
    @15
    @16
    @6
    cxr
    wcel
    #
    @22
    @19
    @15
    @6
    @20
    rexrd
    #
    @5
    @6
    icombl
    syl2anc
    #
    @7
    volge0
    syl
    @15
    @10
    cr
    wcel
    #
    @17
    @12
    cr
    wcel
    wph
    cX
    cr
    @4
    cA
    hoidifhspdmvle.a
    ffvelrnda
    #
    @20
    @10
    @6
    volicore
    syl2anc
    @15
    @22
    @11
    @21
    wcel
    #
    @7
    @11
    wss
    #
    @8
    @12
    cle
    wbr
    @25
    @15
    @26
    @23
    @28
    @27
    @24
    @10
    @6
    icombl
    syl2anc
    @15
    @10
    cxr
    wcel
    @23
    @10
    @5
    cle
    wbr
    #
    @6
    @6
    cle
    wbr
    @29
    @15
    @10
    @27
    rexrd
    @24
    @15
    @4
    cK
    wceq
    #
    @30
    @15
    @31
    wa
    #
    @10
    cY
    @10
    cle
    wbr
    @10
    cY
    cif
    #
    @5
    cle
    @32
    cY
    cr
    wcel
    #
    @26
    @10
    @33
    cle
    wbr
    @15
    @34
    @31
    wph
    @34
    @14
    hoidifhspdmvle.y
    adantr
    #
    adantr
    @15
    @26
    @31
    @27
    adantr
    cY
    @10
    max2
    syl2anc
    @32
    @5
    @31
    @33
    @10
    cif
    #
    @33
    @15
    @5
    @36
    wceq
    #
    @31
    @15
    vx
    cA
    cD
    vh
    @4
    cK
    cfn
    cX
    cY
    vc
    hoidifhspdmvle.d
    @35
    wph
    cX
    cfn
    wcel
    @14
    hoidifhspdmvle.x
    adantr
    wph
    cX
    cr
    cA
    wf
    @14
    hoidifhspdmvle.a
    adantr
    wph
    @14
    simpr
    hoidifhspval3
    #
    adantr
    @31
    @36
    @33
    wceq
    @15
    @31
    @33
    @10
    iftrue
    adantl
    eqtr2d
    breqtrd
    @15
    @31
    wn
    #
    wa
    #
    @10
    @10
    @5
    cle
    @15
    @10
    @10
    cle
    wbr
    @39
    @15
    @10
    @27
    leidd
    adantr
    @40
    @5
    @36
    @10
    @15
    @37
    @39
    @38
    adantr
    @39
    @36
    @10
    wceq
    @15
    @31
    @33
    @10
    iffalse
    adantl
    eqtr2d
    breqtrd
    pm2.61dan
    @15
    @6
    @20
    leidd
    @10
    @6
    @5
    @6
    icossico
    syl22anc
    @7
    @11
    volss
    syl3anc
    fprodle
    wph
    @2
    @9
    @3
    @13
    cle
    wph
    vx
    @0
    cB
    vk
    cL
    cX
    va
    vb
    hoidifhspdmvle.l
    hoidifhspdmvle.x
    wph
    cK
    cX
    wcel
    cX
    c0
    wne
    hoidifhspdmvle.k
    cX
    cK
    ne0i
    syl
    #
    @18
    hoidifhspdmvle.b
    hoidmvn0val
    wph
    vx
    cA
    cB
    vk
    cL
    cX
    va
    vb
    hoidifhspdmvle.l
    hoidifhspdmvle.x
    @41
    hoidifhspdmvle.a
    hoidifhspdmvle.b
    hoidmvn0val
    breq12d
    mpbird
end
