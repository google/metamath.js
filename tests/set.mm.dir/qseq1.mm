include "wceq.mm"
include "cv.mm"
include "cec.mm"
include "wrex.mm"
include "cab.mm"
include "cqs.mm"
include "rexeq.mm"
include "abbidv.mm"
include "df-qs.mm"
include "3eqtr4g.mm"

theorem qseq1
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( A = B -> ( A /. C ) = ( B /. C ) )

  proof
    cA
    cB
    wceq
    #
    vy
    cv
    vx
    cv
    cC
    cec
    wceq
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
    cC
    cqs
    cB
    cC
    cqs
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
    vx
    vy
    cA
    cC
    df-qs
    vx
    vy
    cB
    cC
    df-qs
    3eqtr4g
end
