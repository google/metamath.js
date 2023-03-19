include "wprt.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cec.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "prtlem18.mm"
include "imp.mm"
include "vex.mm"
include "elec.mm"
include "syl6bbr.mm"
include "eqrdv.mm"
include "ex.mm"

theorem prtlem19
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let c.sm: class .~
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r
  let vw: setvar w
  let cS: class S
  assume prtlem18.1: |- .~ = { <. x , y >. | E. u e. A ( x e. u /\ y e. u ) }

  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint .~ v
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
  disjoint u w
  disjoint v w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint .~ p
  disjoint .~ w
  disjoint S v
  disjoint S w
  disjoint S z
  assert |- ( Prt A -> ( ( v e. A /\ z e. v ) -> v = [ z ] .~ ) )

  proof
    cA
    wprt
    #
    vv
    cv
    #
    cA
    wcel
    vz
    cv
    #
    @1
    wcel
    wa
    #
    @1
    @2
    c.sm
    cec
    #
    wceq
    @0
    @3
    wa
    #
    vw
    @1
    @4
    @5
    vw
    cv
    #
    @1
    wcel
    #
    @2
    @6
    c.sm
    wbr
    #
    @6
    @4
    wcel
    @0
    @3
    @7
    @8
    wb
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    c.sm
    prtlem18.1
    prtlem18
    imp
    @6
    @2
    c.sm
    vw
    vex
    vz
    vex
    elec
    syl6bbr
    eqrdv
    ex
end
