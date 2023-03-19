include "cv.mm"
include "wcel.mm"
include "wo.mm"
include "cab.mm"
include "cpr.mm"
include "wa.mm"
include "wex.mm"
include "cun.mm"
include "cuni.mm"
include "wceq.mm"
include "19.43.mm"
include "vex.mm"
include "elpr.mm"
include "anbi2i.mm"
include "andi.mm"
include "bitri.mm"
include "exbii.mm"
include "clel3.mm"
include "exancom.mm"
include "orbi12i.mm"
include "3bitr4ri.mm"
include "abbii.mm"
include "df-un.mm"
include "df-uni.mm"
include "3eqtr4ri.mm"

theorem unipr
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  assume unipr.1: |- A e. _V
  assume unipr.2: |- B e. _V


  assert |- U. { A , B } = ( A u. B )

  proof
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cB
    wcel
    #
    wo
    #
    vx
    cab
    @0
    vy
    cv
    #
    wcel
    #
    @4
    cA
    cB
    cpr
    #
    wcel
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    cA
    cB
    cun
    @6
    cuni
    @3
    @9
    vx
    @5
    @4
    cA
    wceq
    #
    wa
    #
    @5
    @4
    cB
    wceq
    #
    wa
    #
    wo
    #
    vy
    wex
    @11
    vy
    wex
    #
    @13
    vy
    wex
    #
    wo
    @9
    @3
    @11
    @13
    vy
    19.43
    @8
    @14
    vy
    @8
    @5
    @10
    @12
    wo
    #
    wa
    @14
    @7
    @17
    @5
    @4
    cA
    cB
    vy
    vex
    elpr
    anbi2i
    @5
    @10
    @12
    andi
    bitri
    exbii
    @1
    @15
    @2
    @16
    @1
    @10
    @5
    wa
    vy
    wex
    @15
    vy
    @0
    cA
    unipr.1
    clel3
    @10
    @5
    vy
    exancom
    bitri
    @2
    @12
    @5
    wa
    vy
    wex
    @16
    vy
    @0
    cB
    unipr.2
    clel3
    @12
    @5
    vy
    exancom
    bitri
    orbi12i
    3bitr4ri
    abbii
    vx
    cA
    cB
    df-un
    vx
    vy
    @6
    df-uni
    3eqtr4ri
end
