include "cun.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "wo.mm"
include "19.43.mm"
include "elun.mm"
include "anbi2i.mm"
include "andi.mm"
include "bitri.mm"
include "exbii.mm"
include "eluni.mm"
include "orbi12i.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem uniun
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- U. ( A u. B ) = ( U. A u. U. B )

  proof
    vx
    cA
    cB
    cun
    #
    cuni
    #
    cA
    cuni
    #
    cB
    cuni
    #
    cun
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
    wo
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
    wo
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
    wo
    @10
    @13
    @15
    @17
    vy
    19.43
    @9
    @18
    vy
    @9
    @7
    @14
    @16
    wo
    #
    wa
    @18
    @8
    @21
    @7
    @6
    cA
    cB
    elun
    anbi2i
    @7
    @14
    @16
    andi
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
    orbi12i
    3bitr4i
    vy
    @5
    @0
    eluni
    @5
    @2
    @3
    elun
    3bitr4i
    eqriv
end
