include "c0.mm"
include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cop.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "vex.mm"
include "opnzi.mm"
include "nesymi.mm"
include "intnanr.mm"
include "nex.mm"
include "elxp.mm"
include "mtbir.mm"

theorem 0nelxp
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let cC: class C


  assert |- -. (/) e. ( A X. B )

  proof
    c0
    cA
    cB
    cxp
    wcel
    c0
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    wceq
    #
    @0
    cA
    wcel
    @1
    cB
    wcel
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    wex
    @6
    vx
    @5
    vy
    @3
    @4
    @2
    c0
    @0
    @1
    vx
    vex
    vy
    vex
    opnzi
    nesymi
    intnanr
    nex
    nex
    vx
    vy
    c0
    cA
    cB
    elxp
    mtbir
end
