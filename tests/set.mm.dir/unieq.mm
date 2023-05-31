include "wceq.mm"
include "wel.mm"
include "wrex.mm"
include "cab.mm"
include "cuni.mm"
include "rexeq.mm"
include "abbidv.mm"
include "dfuni2.mm"
include "3eqtr4g.mm"

theorem unieq
  param cA: class A
  param cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( A = B -> U. A = U. B )

  proof
    cA
    cB
    wceq
    #
    vy
    vx
    wel
    #
    vx
    cA
    wrex
    #
    vy
    cab
    @1
    vx
    cB
    wrex
    #
    vy
    cab
    cA
    cuni
    cB
    cuni
    @0
    @2
    @3
    vy
    @1
    vx
    cA
    cB
    rexeq
    abbidv
    vy
    vx
    cA
    dfuni2
    vy
    vx
    cB
    dfuni2
    3eqtr4g
end
