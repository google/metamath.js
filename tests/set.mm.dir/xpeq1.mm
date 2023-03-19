include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "cxp.mm"
include "eleq2.mm"
include "anbi1d.mm"
include "opabbidv.mm"
include "df-xp.mm"
include "3eqtr4g.mm"

theorem xpeq1
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A = B -> ( A X. C ) = ( B X. C ) )

  proof
    cA
    cB
    wceq
    #
    vx
    cv
    #
    cA
    wcel
    #
    vy
    cv
    cC
    wcel
    #
    wa
    #
    vx
    vy
    copab
    @1
    cB
    wcel
    #
    @3
    wa
    #
    vx
    vy
    copab
    cA
    cC
    cxp
    cB
    cC
    cxp
    @0
    @4
    @6
    vx
    vy
    @0
    @2
    @5
    @3
    cA
    cB
    @1
    eleq2
    anbi1d
    opabbidv
    vx
    vy
    cA
    cC
    df-xp
    vx
    vy
    cB
    cC
    df-xp
    3eqtr4g
end
