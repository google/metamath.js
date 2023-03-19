include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "copab.mm"
include "cxp.mm"
include "eleq2.mm"
include "anbi2d.mm"
include "opabbidv.mm"
include "df-xp.mm"
include "3eqtr4g.mm"

theorem xpeq2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A = B -> ( C X. A ) = ( C X. B ) )

  proof
    cA
    cB
    wceq
    #
    vx
    cv
    cC
    wcel
    #
    vy
    cv
    #
    cA
    wcel
    #
    wa
    #
    vx
    vy
    copab
    @1
    @2
    cB
    wcel
    #
    wa
    #
    vx
    vy
    copab
    cC
    cA
    cxp
    cC
    cB
    cxp
    @0
    @4
    @6
    vx
    vy
    @0
    @3
    @5
    @1
    cA
    cB
    @2
    eleq2
    anbi2d
    opabbidv
    vx
    vy
    cC
    cA
    df-xp
    vx
    vy
    cC
    cB
    df-xp
    3eqtr4g
end
