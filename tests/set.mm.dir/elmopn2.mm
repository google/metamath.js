include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "wa.mm"
include "cbl.mm"
include "crn.mm"
include "wrex.mm"
include "wral.mm"
include "co.mm"
include "crp.mm"
include "elmopn.mm"
include "wb.mm"
include "ssel2.mm"
include "blssex.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "pm5.32da.mm"
include "bitrd.mm"

theorem elmopn2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cJ: class J
  let cX: class X
  let vz: setvar z
  let vd: setvar d
  assume mopnval.1: |- J = ( MetOpen ` D )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint D x
  disjoint D y
  disjoint X x
  disjoint X y
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint D d
  disjoint D z
  disjoint X z
  assert |- ( D e. ( *Met ` X ) -> ( A e. J <-> ( A C_ X /\ A. x e. A E. y e. RR+ ( x ( ball ` D ) y ) C_ A ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cA
    cJ
    wcel
    cA
    cX
    wss
    #
    vx
    cv
    #
    vz
    cv
    #
    wcel
    @3
    cA
    wss
    wa
    vz
    cD
    cbl
    cfv
    #
    crn
    wrex
    #
    vx
    cA
    wral
    #
    wa
    @1
    @2
    vy
    cv
    @4
    co
    cA
    wss
    vy
    crp
    wrex
    #
    vx
    cA
    wral
    #
    wa
    vx
    vz
    cA
    cD
    cJ
    cX
    mopnval.1
    elmopn
    @0
    @1
    @6
    @8
    @0
    @1
    wa
    @5
    @7
    vx
    cA
    @0
    @1
    @2
    cA
    wcel
    #
    @5
    @7
    wb
    #
    @1
    @9
    wa
    @0
    @2
    cX
    wcel
    @10
    cA
    cX
    @2
    ssel2
    vz
    cA
    cD
    @2
    cX
    vy
    blssex
    sylan2
    anassrs
    ralbidva
    pm5.32da
    bitrd
end
