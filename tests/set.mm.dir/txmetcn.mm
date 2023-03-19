include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "wral.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "crp.mm"
include "wrex.mm"
include "ctopon.mm"
include "wb.mm"
include "mopntopon.mm"
include "txtopon.mm"
include "syl2an.mm"
include "3adant3.mm"
include "3ad2ant3.mm"
include "cncnp.mm"
include "syl2anc.mm"
include "cop.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "ralxp.mm"
include "txmetcnp.mm"
include "adantlr.mm"
include "simplr.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "2ralbidva.mm"
include "syl5bb.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem txmetcn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cP: class P
  assume metcn.2: |- J = ( MetOpen ` C )
  assume metcn.4: |- K = ( MetOpen ` D )
  assume txmetcnp.4: |- L = ( MetOpen ` E )

  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint C u
  disjoint C v
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D u
  disjoint D v
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint J t
  disjoint K t
  disjoint X t
  disjoint Y t
  disjoint Z t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B z
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint L t
  assert |- ( ( C e. ( *Met ` X ) /\ D e. ( *Met ` Y ) /\ E e. ( *Met ` Z ) ) -> ( F e. ( ( J tX K ) Cn L ) <-> ( F : ( X X. Y ) --> Z /\ A. x e. X A. y e. Y A. z e. RR+ E. w e. RR+ A. u e. X A. v e. Y ( ( ( x C u ) < w /\ ( y D v ) < w ) -> ( ( x F y ) E ( u F v ) ) < z ) ) ) )

  proof
    cC
    cX
    cxmt
    cfv
    wcel
    #
    cD
    cY
    cxmt
    cfv
    wcel
    #
    cE
    cZ
    cxmt
    cfv
    wcel
    #
    w3a
    #
    cF
    cJ
    cK
    ctx
    co
    #
    cL
    ccn
    co
    wcel
    #
    cX
    cY
    cxp
    #
    cZ
    cF
    wf
    #
    cF
    vt
    cv
    #
    @4
    cL
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    vt
    @6
    wral
    #
    wa
    #
    @7
    vx
    cv
    #
    vu
    cv
    #
    cC
    co
    vw
    cv
    #
    clt
    wbr
    vy
    cv
    #
    vv
    cv
    #
    cD
    co
    @16
    clt
    wbr
    wa
    @14
    @17
    cF
    co
    @15
    @18
    cF
    co
    cE
    co
    vz
    cv
    clt
    wbr
    wi
    vv
    cY
    wral
    vu
    cX
    wral
    vw
    crp
    wrex
    vz
    crp
    wral
    #
    vy
    cY
    wral
    vx
    cX
    wral
    #
    wa
    @3
    @4
    @6
    ctopon
    cfv
    wcel
    #
    cL
    cZ
    ctopon
    cfv
    wcel
    #
    @5
    @13
    wb
    @0
    @1
    @21
    @2
    @0
    cJ
    cX
    ctopon
    cfv
    wcel
    cK
    cY
    ctopon
    cfv
    wcel
    @21
    @1
    cC
    cJ
    cX
    metcn.2
    mopntopon
    cD
    cK
    cY
    metcn.4
    mopntopon
    cJ
    cK
    cX
    cY
    txtopon
    syl2an
    3adant3
    @2
    @0
    @22
    @1
    cE
    cL
    cZ
    txmetcnp.4
    mopntopon
    3ad2ant3
    vt
    cF
    @4
    cL
    @6
    cZ
    cncnp
    syl2anc
    @3
    @7
    @12
    @20
    @12
    cF
    @14
    @17
    cop
    #
    @9
    cfv
    #
    wcel
    #
    vy
    cY
    wral
    vx
    cX
    wral
    @3
    @7
    wa
    #
    @20
    @11
    @25
    vt
    vx
    vy
    cX
    cY
    @8
    @23
    wceq
    @10
    @24
    cF
    @8
    @23
    @9
    fveq2
    eleq2d
    ralxp
    @26
    @25
    @19
    vx
    vy
    cX
    cY
    @26
    @14
    cX
    wcel
    @17
    cY
    wcel
    wa
    #
    wa
    #
    @25
    @7
    @19
    wa
    #
    @19
    @3
    @27
    @25
    @29
    wb
    @7
    vz
    vw
    vv
    vu
    @14
    @17
    cC
    cD
    cE
    cF
    cJ
    cK
    cL
    cX
    cY
    cZ
    metcn.2
    metcn.4
    txmetcnp.4
    txmetcnp
    adantlr
    @28
    @7
    @19
    @3
    @7
    @27
    simplr
    biantrurd
    bitr4d
    2ralbidva
    syl5bb
    pm5.32da
    bitrd
end
