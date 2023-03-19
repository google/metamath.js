include "cv.mm"
include "wwe.mm"
include "wex.mm"
include "wceq.mm"
include "weeq2.mm"
include "exbidv.mm"
include "dfac8.mm"
include "axaci.mm"
include "vtoclg.mm"

theorem weth
  let vx: setvar x
  let cA: class A
  let cV: class V
  let vy: setvar y

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- ( A e. V -> E. x x We A )

  proof
    vy
    cv
    #
    vx
    cv
    #
    wwe
    #
    vx
    wex
    #
    cA
    @1
    wwe
    #
    vx
    wex
    vy
    cA
    cV
    @0
    cA
    wceq
    @2
    @4
    vx
    @0
    cA
    @1
    weeq2
    exbidv
    @3
    vy
    vy
    vx
    dfac8
    axaci
    vtoclg
end
