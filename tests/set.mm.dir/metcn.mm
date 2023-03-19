include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "ccn.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "wral.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "crp.mm"
include "wrex.mm"
include "ctopon.mm"
include "wb.mm"
include "mopntopon.mm"
include "cncnp.mm"
include "syl2an.mm"
include "metcnp.mm"
include "3expa.mm"
include "adantlr.mm"
include "simplr.mm"
include "biantrurd.mm"
include "bitr4d.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem metcn
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cC: class C
  let cD: class D
  let cF: class F
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let cZ: class Z
  let cA: class A
  let cB: class B
  let cE: class E
  let cP: class P
  let cL: class L
  assume metcn.2: |- J = ( MetOpen ` C )
  assume metcn.4: |- K = ( MetOpen ` D )

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
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint K w
  disjoint K x
  disjoint K y
  disjoint K z
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Y w
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint F t
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
  disjoint J t
  disjoint J u
  disjoint J v
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint X t
  disjoint X u
  disjoint X v
  disjoint Y t
  disjoint Y u
  disjoint Y v
  disjoint Z t
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint C u
  disjoint C v
  disjoint D u
  disjoint D v
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint B x
  disjoint B z
  disjoint E u
  disjoint E v
  disjoint E w
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint P u
  disjoint P v
  disjoint P w
  disjoint P x
  disjoint P y
  disjoint P z
  disjoint L t
  disjoint L w
  disjoint L x
  disjoint L y
  disjoint L z
  assert |- ( ( C e. ( *Met ` X ) /\ D e. ( *Met ` Y ) ) -> ( F e. ( J Cn K ) <-> ( F : X --> Y /\ A. x e. X A. y e. RR+ E. z e. RR+ A. w e. X ( ( x C w ) < z -> ( ( F ` x ) D ( F ` w ) ) < y ) ) ) )

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
    wa
    #
    cF
    cJ
    cK
    ccn
    co
    wcel
    #
    cX
    cY
    cF
    wf
    #
    cF
    vx
    cv
    #
    cJ
    cK
    ccnp
    co
    cfv
    wcel
    #
    vx
    cX
    wral
    #
    wa
    #
    @4
    @5
    vw
    cv
    #
    cC
    co
    vz
    cv
    clt
    wbr
    @5
    cF
    cfv
    @9
    cF
    cfv
    cD
    co
    vy
    cv
    clt
    wbr
    wi
    vw
    cX
    wral
    vz
    crp
    wrex
    vy
    crp
    wral
    #
    vx
    cX
    wral
    #
    wa
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
    @3
    @8
    wb
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
    vx
    cF
    cJ
    cK
    cX
    cY
    cncnp
    syl2an
    @2
    @4
    @7
    @11
    @2
    @4
    wa
    #
    @6
    @10
    vx
    cX
    @12
    @5
    cX
    wcel
    #
    wa
    #
    @6
    @4
    @10
    wa
    #
    @10
    @2
    @13
    @6
    @15
    wb
    #
    @4
    @0
    @1
    @13
    @16
    vy
    vz
    vw
    cC
    cD
    @5
    cF
    cJ
    cK
    cX
    cY
    metcn.2
    metcn.4
    metcnp
    3expa
    adantlr
    @14
    @4
    @10
    @2
    @4
    @13
    simplr
    biantrurd
    bitr4d
    ralbidva
    pm5.32da
    bitrd
end
