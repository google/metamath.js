include "wss.mm"
include "cuni.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wex.mm"
include "ssel.mm"
include "anim2d.mm"
include "eximdv.mm"
include "eluni.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem uniss
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C


  assert |- ( A C_ B -> U. A C_ U. B )

  proof
    cA
    cB
    wss
    #
    vx
    cA
    cuni
    #
    cB
    cuni
    #
    @0
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    @4
    cA
    wcel
    #
    wa
    #
    vy
    wex
    @5
    @4
    cB
    wcel
    #
    wa
    #
    vy
    wex
    @3
    @1
    wcel
    @3
    @2
    wcel
    @0
    @7
    @9
    vy
    @0
    @6
    @8
    @5
    cA
    cB
    @4
    ssel
    anim2d
    eximdv
    vy
    @3
    cA
    eluni
    vy
    @3
    cB
    eluni
    3imtr4g
    ssrdv
end
