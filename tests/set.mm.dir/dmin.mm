include "cin.mm"
include "cdm.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "19.40.mm"
include "vex.mm"
include "eldm2.mm"
include "elin.mm"
include "exbii.mm"
include "bitri.mm"
include "anbi12i.mm"
include "3imtr4i.mm"
include "ssriv.mm"

theorem dmin
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cR: class R


  assert |- dom ( A i^i B ) C_ ( dom A i^i dom B )

  proof
    vx
    cA
    cB
    cin
    #
    cdm
    #
    cA
    cdm
    #
    cB
    cdm
    #
    cin
    #
    vx
    cv
    #
    vy
    cv
    cop
    #
    cA
    wcel
    #
    @6
    cB
    wcel
    #
    wa
    #
    vy
    wex
    #
    @7
    vy
    wex
    #
    @8
    vy
    wex
    #
    wa
    #
    @5
    @1
    wcel
    #
    @5
    @4
    wcel
    #
    @7
    @8
    vy
    19.40
    @14
    @6
    @0
    wcel
    #
    vy
    wex
    @10
    vy
    @5
    @0
    vx
    vex
    #
    eldm2
    @16
    @9
    vy
    @6
    cA
    cB
    elin
    exbii
    bitri
    @15
    @5
    @2
    wcel
    #
    @5
    @3
    wcel
    #
    wa
    @13
    @5
    @2
    @3
    elin
    @18
    @11
    @19
    @12
    vy
    @5
    cA
    @17
    eldm2
    vy
    @5
    cB
    @17
    eldm2
    anbi12i
    bitri
    3imtr4i
    ssriv
end
