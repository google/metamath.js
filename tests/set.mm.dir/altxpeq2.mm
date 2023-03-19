include "wceq.mm"
include "cv.mm"
include "caltop.mm"
include "wrex.mm"
include "cab.mm"
include "caltxp.mm"
include "rexeq.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "df-altxp.mm"
include "3eqtr4g.mm"

theorem altxpeq2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A = B -> ( C XX. A ) = ( C XX. B ) )

  proof
    cA
    cB
    wceq
    #
    vz
    cv
    vx
    cv
    vy
    cv
    caltop
    wceq
    #
    vy
    cA
    wrex
    #
    vx
    cC
    wrex
    #
    vz
    cab
    @1
    vy
    cB
    wrex
    #
    vx
    cC
    wrex
    #
    vz
    cab
    cC
    cA
    caltxp
    cC
    cB
    caltxp
    @0
    @3
    @5
    vz
    @0
    @2
    @4
    vx
    cC
    @1
    vy
    cA
    cB
    rexeq
    rexbidv
    abbidv
    vx
    vy
    vz
    cC
    cA
    df-altxp
    vx
    vy
    vz
    cC
    cB
    df-altxp
    3eqtr4g
end
