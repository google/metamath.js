include "wprt.mm"
include "wel.mm"
include "wa.mm"
include "wrex.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "anabs7.mm"
include "an43.mm"
include "anbi2i.mm"
include "3bitr4ri.mm"
include "weq.mm"
include "prtlem14.mm"
include "an3.mm"
include "elequ2.mm"
include "anbi2d.mm"
include "syl5ibr.mm"
include "syl8.mm"
include "imp4a.mm"
include "syl7bi.mm"
include "expdimp.mm"
include "rexlimdv.mm"
include "reximdva.mm"
include "anbi12d.mm"
include "cbvrexv.mm"
include "syl6ib.mm"

theorem prtlem15
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A

  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A x
  disjoint A y
  disjoint A z
  assert |- ( Prt A -> ( E. x e. A E. y e. A ( ( u e. x /\ w e. x ) /\ ( w e. y /\ v e. y ) ) -> E. z e. A ( u e. z /\ v e. z ) ) )

  proof
    cA
    wprt
    #
    vu
    vx
    wel
    #
    vw
    vx
    wel
    #
    wa
    vw
    vy
    wel
    #
    vv
    vy
    wel
    #
    wa
    wa
    #
    vy
    cA
    wrex
    #
    vx
    cA
    wrex
    @1
    vv
    vx
    wel
    #
    wa
    #
    vx
    cA
    wrex
    vu
    vz
    wel
    #
    vv
    vz
    wel
    #
    wa
    #
    vz
    cA
    wrex
    @0
    @6
    @8
    vx
    cA
    @0
    vx
    cv
    cA
    wcel
    #
    wa
    @5
    @8
    vy
    cA
    @0
    @12
    vy
    cv
    cA
    wcel
    #
    @5
    @8
    wi
    #
    @5
    @2
    @3
    wa
    #
    @5
    wa
    #
    @0
    @12
    @13
    wa
    #
    @8
    @15
    @1
    @4
    wa
    #
    @15
    wa
    #
    wa
    @19
    @16
    @5
    @18
    @15
    anabs7
    @5
    @19
    @15
    @1
    @2
    @3
    @4
    an43
    #
    anbi2i
    @20
    3bitr4ri
    @0
    @17
    @15
    @5
    @8
    @0
    @17
    @15
    vx
    vy
    weq
    #
    @14
    vx
    vy
    vw
    cA
    prtlem14
    @5
    @8
    @21
    @18
    @1
    @2
    @3
    @4
    an3
    @21
    @7
    @4
    @1
    vx
    vy
    vv
    elequ2
    anbi2d
    syl5ibr
    syl8
    imp4a
    syl7bi
    expdimp
    rexlimdv
    reximdva
    @8
    @11
    vx
    vz
    cA
    vx
    vz
    weq
    @1
    @9
    @7
    @10
    vx
    vz
    vu
    elequ2
    vx
    vz
    vv
    elequ2
    anbi12d
    cbvrexv
    syl6ib
end
