include "cfv.mm"
include "co.mm"
include "cv.mm"
include "cico.mm"
include "cvol.mm"
include "cprod.mm"
include "csn.mm"
include "cdif.mm"
include "cmul.mm"
include "cun.mm"
include "cfn.mm"
include "wcel.mm"
include "snfi.mm"
include "a1i.mm"
include "unfi.mm"
include "syl2anc.mm"
include "syl5eqel.mm"
include "c0.mm"
include "wne.mm"
include "snidg.mm"
include "syl.mm"
include "elun2.mm"
include "syl6eleqr.mm"
include "ne0i.mm"
include "hoidmvn0val.mm"
include "wa.mm"
include "cr.mm"
include "ffvelrnda.mm"
include "volicore.mm"
include "recnd.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "adantl.mm"
include "fprodsplit1.mm"
include "difeq1i.mm"
include "difun2.mm"
include "wn.mm"
include "difsn.mm"
include "3eqtrd.mm"
include "prodeq1d.mm"
include "eqcomi.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "ffvelrnd.mm"
include "wf.mm"
include "adantr.mm"
include "ssun1.mm"
include "sseqtr4i.mm"
include "id.mm"
include "sseldi.mm"
include "fprodrecl.mm"
include "mulcomd.mm"

theorem hoiprodp1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cG: class G
  let cL: class L
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  assume hoiprodp1.l: |- L = ( x e. Fin |-> ( a e. ( RR ^m x ) , b e. ( RR ^m x ) |-> if ( x = (/) , 0 , prod_ k e. x ( vol ` ( ( a ` k ) [,) ( b ` k ) ) ) ) ) )
  assume hoiprodp1.y: |- ( ph -> Y e. Fin )
  assume hoiprodp1.3: |- ( ph -> Z e. V )
  assume hoiprodp1.z: |- ( ph -> -. Z e. Y )
  assume hoiprodp1.x: |- X = ( Y u. { Z } )
  assume hoiprodp1.a: |- ( ph -> A : X --> RR )
  assume hoiprodp1.b: |- ( ph -> B : X --> RR )
  assume hoiprodp1.g: |- G = prod_ k e. Y ( vol ` ( ( A ` k ) [,) ( B ` k ) ) )

  disjoint A a
  disjoint A b
  disjoint A k
  disjoint a b
  disjoint a k
  disjoint b k
  disjoint B a
  disjoint B b
  disjoint B k
  disjoint X a
  disjoint X b
  disjoint X k
  disjoint X x
  disjoint a x
  disjoint b x
  disjoint k x
  disjoint Y k
  disjoint Z k
  disjoint a ph
  disjoint b ph
  disjoint k ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> ( A ( L ` X ) B ) = ( G x. ( vol ` ( ( A ` Z ) [,) ( B ` Z ) ) ) ) )

  proof
    wph
    cA
    cB
    cX
    cL
    cfv
    co
    cX
    vk
    cv
    #
    cA
    cfv
    #
    @0
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
    cZ
    cA
    cfv
    #
    cZ
    cB
    cfv
    #
    cico
    co
    #
    cvol
    cfv
    #
    cX
    cZ
    csn
    #
    cdif
    #
    @4
    vk
    cprod
    #
    cmul
    co
    #
    cG
    @8
    cmul
    co
    #
    wph
    vx
    cA
    cB
    vk
    cL
    cX
    va
    vb
    hoiprodp1.l
    wph
    cX
    cY
    @9
    cun
    #
    cfn
    hoiprodp1.x
    wph
    cY
    cfn
    wcel
    @9
    cfn
    wcel
    #
    @14
    cfn
    wcel
    hoiprodp1.y
    @15
    wph
    cZ
    snfi
    a1i
    cY
    @9
    unfi
    syl2anc
    syl5eqel
    #
    wph
    cZ
    cX
    wcel
    cX
    c0
    wne
    wph
    cZ
    @14
    cX
    wph
    cZ
    @9
    wcel
    #
    cZ
    @14
    wcel
    wph
    cZ
    cV
    wcel
    @17
    hoiprodp1.3
    cZ
    cV
    snidg
    syl
    cZ
    @9
    cY
    elun2
    syl
    hoiprodp1.x
    syl6eleqr
    #
    cX
    cZ
    ne0i
    syl
    hoiprodp1.a
    hoiprodp1.b
    hoidmvn0val
    wph
    cX
    @4
    cZ
    @8
    vk
    @16
    wph
    @0
    cX
    wcel
    #
    wa
    #
    @4
    @20
    @1
    cr
    wcel
    #
    @2
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    wph
    cX
    cr
    @0
    cA
    hoiprodp1.a
    ffvelrnda
    wph
    cX
    cr
    @0
    cB
    hoiprodp1.b
    ffvelrnda
    @1
    @2
    volicore
    #
    syl2anc
    recnd
    @18
    @0
    cZ
    wceq
    #
    @4
    @8
    wceq
    wph
    @25
    @3
    @7
    cvol
    @25
    @1
    @5
    @2
    @6
    cico
    @0
    cZ
    cA
    fveq2
    @0
    cZ
    cB
    fveq2
    oveq12d
    fveq2d
    adantl
    fprodsplit1
    wph
    @12
    @8
    cG
    cmul
    co
    @13
    wph
    @11
    cG
    @8
    cmul
    wph
    @11
    cY
    @4
    vk
    cprod
    #
    cG
    wph
    @10
    cY
    @4
    vk
    wph
    @10
    @14
    @9
    cdif
    #
    cY
    @9
    cdif
    #
    cY
    @10
    @27
    wceq
    wph
    cX
    @14
    @9
    hoiprodp1.x
    difeq1i
    a1i
    @27
    @28
    wceq
    wph
    cY
    @9
    difun2
    a1i
    wph
    cZ
    cY
    wcel
    wn
    @28
    cY
    wceq
    hoiprodp1.z
    cZ
    cY
    difsn
    syl
    3eqtrd
    prodeq1d
    @26
    cG
    wceq
    wph
    cG
    @26
    hoiprodp1.g
    eqcomi
    a1i
    eqtrd
    oveq2d
    wph
    @8
    cG
    wph
    @8
    wph
    @5
    cr
    wcel
    @6
    cr
    wcel
    @8
    cr
    wcel
    wph
    cX
    cr
    cZ
    cA
    hoiprodp1.a
    @18
    ffvelrnd
    wph
    cX
    cr
    cZ
    cB
    hoiprodp1.b
    @18
    ffvelrnd
    @5
    @6
    volicore
    syl2anc
    recnd
    wph
    cG
    wph
    cG
    @26
    cr
    hoiprodp1.g
    wph
    cY
    @4
    vk
    hoiprodp1.y
    wph
    @0
    cY
    wcel
    #
    wa
    #
    @21
    @22
    @23
    @30
    cX
    cr
    @0
    cA
    wph
    cX
    cr
    cA
    wf
    @29
    hoiprodp1.a
    adantr
    @29
    @19
    wph
    @29
    cY
    cX
    @0
    cY
    @14
    cX
    cY
    @9
    ssun1
    hoiprodp1.x
    sseqtr4i
    @29
    id
    sseldi
    adantl
    #
    ffvelrnd
    @30
    cX
    cr
    @0
    cB
    wph
    cX
    cr
    cB
    wf
    @29
    hoiprodp1.b
    adantr
    @31
    ffvelrnd
    @24
    syl2anc
    fprodrecl
    syl5eqel
    recnd
    mulcomd
    eqtrd
    3eqtrd
end
