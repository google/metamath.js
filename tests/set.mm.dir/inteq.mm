include "wceq.mm"
include "wel.mm"
include "wral.mm"
include "cab.mm"
include "cint.mm"
include "raleq.mm"
include "abbidv.mm"
include "dfint2.mm"
include "3eqtr4g.mm"

theorem inteq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( A = B -> |^| A = |^| B )

  proof
    cA
    cB
    wceq
    #
    vx
    vy
    wel
    #
    vy
    cA
    wral
    #
    vx
    cab
    @1
    vy
    cB
    wral
    #
    vx
    cab
    cA
    cint
    cB
    cint
    @0
    @2
    @3
    vx
    @1
    vy
    cA
    cB
    raleq
    abbidv
    vx
    vy
    cA
    dfint2
    vx
    vy
    cB
    dfint2
    3eqtr4g
end
