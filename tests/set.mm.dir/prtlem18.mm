include "wprt.mm"
include "cv.mm"
include "wcel.mm"
include "wel.mm"
include "wa.mm"
include "wbr.mm"
include "wi.mm"
include "wrex.mm"
include "rspe.mm"
include "expr.mm"
include "prtlem13.mm"
include "syl6ibr.mm"
include "a1i.mm"
include "prtlem17.mm"
include "syl7bi.mm"
include "impbidd.mm"

theorem prtlem18
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let c.sm: class .~
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let cS: class S
  assume prtlem18.1: |- .~ = { <. x , y >. | E. u e. A ( x e. u /\ y e. u ) }

  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint .~ v
  disjoint .~ w
  disjoint .~ z
  disjoint p q
  disjoint p r
  disjoint p u
  disjoint p v
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint A p
  disjoint q r
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint A q
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint .~ p
  disjoint S v
  disjoint S w
  disjoint S z
  assert |- ( Prt A -> ( ( v e. A /\ z e. v ) -> ( w e. v <-> z .~ w ) ) )

  proof
    cA
    wprt
    #
    vv
    cv
    cA
    wcel
    #
    vz
    vv
    wel
    #
    wa
    #
    vw
    vv
    wel
    #
    vz
    cv
    vw
    cv
    c.sm
    wbr
    #
    @3
    @4
    @5
    wi
    wi
    @0
    @3
    @4
    @2
    @4
    wa
    #
    vv
    cA
    wrex
    #
    @5
    @1
    @2
    @4
    @7
    @6
    vv
    cA
    rspe
    expr
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    c.sm
    prtlem18.1
    prtlem13
    syl6ibr
    a1i
    @5
    vz
    vp
    wel
    vw
    vp
    wel
    wa
    vp
    cA
    wrex
    @0
    @3
    @4
    vx
    vy
    vz
    vw
    vp
    vu
    cA
    c.sm
    prtlem18.1
    prtlem13
    vv
    vp
    vz
    vw
    cA
    prtlem17
    syl7bi
    impbidd
end
