include "wceq.mm"
include "cv.mm"
include "caltop.mm"
include "wrex.mm"
include "cab.mm"
include "caltxp.mm"
include "rexeq.mm"
include "abbidv.mm"
include "df-altxp.mm"
include "3eqtr4g.mm"

theorem altxpeq1
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A = B -> ( A XX. C ) = ( B XX. C ) )

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
    vy
    cC
    wrex
    #
    vx
    cA
    wrex
    #
    vz
    cab
    @1
    vx
    cB
    wrex
    #
    vz
    cab
    cA
    cC
    caltxp
    cB
    cC
    caltxp
    @0
    @2
    @3
    vz
    @1
    vx
    cA
    cB
    rexeq
    abbidv
    vx
    vy
    vz
    cA
    cC
    df-altxp
    vx
    vy
    vz
    cB
    cC
    df-altxp
    3eqtr4g
end
