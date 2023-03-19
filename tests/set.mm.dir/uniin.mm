include "cin.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "19.40.mm"
include "elin.mm"
include "anbi2i.mm"
include "anandi.mm"
include "bitri.mm"
include "exbii.mm"
include "eluni.mm"
include "anbi12i.mm"
include "3imtr4i.mm"
include "ssriv.mm"

theorem uniin
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- U. ( A i^i B ) C_ ( U. A i^i U. B )

  proof
    vx
    cA
    cB
    cin
    #
    cuni
    #
    cA
    cuni
    #
    cB
    cuni
    #
    cin
    #
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    @6
    @0
    wcel
    #
    wa
    #
    vy
    wex
    #
    @5
    @2
    wcel
    #
    @5
    @3
    wcel
    #
    wa
    #
    @5
    @1
    wcel
    @5
    @4
    wcel
    @7
    @6
    cA
    wcel
    #
    wa
    #
    @7
    @6
    cB
    wcel
    #
    wa
    #
    wa
    #
    vy
    wex
    @15
    vy
    wex
    #
    @17
    vy
    wex
    #
    wa
    @10
    @13
    @15
    @17
    vy
    19.40
    @9
    @18
    vy
    @9
    @7
    @14
    @16
    wa
    #
    wa
    @18
    @8
    @21
    @7
    @6
    cA
    cB
    elin
    anbi2i
    @7
    @14
    @16
    anandi
    bitri
    exbii
    @11
    @19
    @12
    @20
    vy
    @5
    cA
    eluni
    vy
    @5
    cB
    eluni
    anbi12i
    3imtr4i
    vy
    @5
    @0
    eluni
    @5
    @2
    @3
    elin
    3imtr4i
    ssriv
end
