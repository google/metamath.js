include "wel.mm"
include "wa.mm"
include "wrex.mm"
include "cv.mm"
include "vex.mm"
include "weq.mm"
include "elequ2.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "eleq1.mm"
include "bi2anan9.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "braba.mm"

theorem prtlem13
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let c.sm: class .~
  assume prtlem13.1: |- .~ = { <. x , y >. | E. u e. A ( x e. u /\ y e. u ) }

  disjoint u v
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint v w
  disjoint w x
  disjoint w y
  disjoint v z
  disjoint x z
  disjoint y z
  assert |- ( z .~ w <-> E. v e. A ( z e. v /\ w e. v ) )

  proof
    vx
    vu
    wel
    #
    vy
    vu
    wel
    #
    wa
    #
    vu
    cA
    wrex
    #
    vz
    vv
    wel
    #
    vw
    vv
    wel
    #
    wa
    #
    vv
    cA
    wrex
    #
    vx
    vy
    vz
    cv
    #
    vw
    cv
    #
    c.sm
    vz
    vex
    vw
    vex
    @3
    vx
    vv
    wel
    #
    vy
    vv
    wel
    #
    wa
    #
    vv
    cA
    wrex
    vx
    vz
    weq
    #
    vy
    vw
    weq
    #
    wa
    #
    @7
    @2
    @12
    vu
    vv
    cA
    vu
    vv
    weq
    @0
    @10
    @1
    @11
    vu
    vv
    vx
    elequ2
    vu
    vv
    vy
    elequ2
    anbi12d
    cbvrexv
    @15
    @12
    @6
    vv
    cA
    @13
    @10
    @4
    @14
    @11
    @5
    vx
    cv
    @8
    vv
    cv
    #
    eleq1
    vy
    cv
    @9
    @16
    eleq1
    bi2anan9
    rexbidv
    syl5bb
    prtlem13.1
    braba
end
