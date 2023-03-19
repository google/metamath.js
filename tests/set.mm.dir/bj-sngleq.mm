include "wceq.mm"
include "cv.mm"
include "csn.mm"
include "wrex.mm"
include "cab.mm"
include "bj-csngl.mm"
include "rexeq.mm"
include "abbidv.mm"
include "df-bj-sngl.mm"
include "3eqtr4g.mm"

theorem bj-sngleq
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( A = B -> sngl A = sngl B )

  proof
    cA
    cB
    wceq
    #
    vx
    cv
    vy
    cv
    csn
    wceq
    #
    vy
    cA
    wrex
    #
    vx
    cab
    @1
    vy
    cB
    wrex
    #
    vx
    cab
    cA
    bj-csngl
    cB
    bj-csngl
    @0
    @2
    @3
    vx
    @1
    vy
    cA
    cB
    rexeq
    abbidv
    vx
    vy
    cA
    df-bj-sngl
    vx
    vy
    cB
    df-bj-sngl
    3eqtr4g
end
