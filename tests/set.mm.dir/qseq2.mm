include "wceq.mm"
include "cv.mm"
include "cec.mm"
include "wrex.mm"
include "cab.mm"
include "cqs.mm"
include "eceq2.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "df-qs.mm"
include "3eqtr4g.mm"

theorem qseq2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( A = B -> ( C /. A ) = ( C /. B ) )

  proof
    cA
    cB
    wceq
    #
    vy
    cv
    #
    vx
    cv
    #
    cA
    cec
    #
    wceq
    #
    vx
    cC
    wrex
    #
    vy
    cab
    @1
    @2
    cB
    cec
    #
    wceq
    #
    vx
    cC
    wrex
    #
    vy
    cab
    cC
    cA
    cqs
    cC
    cB
    cqs
    @0
    @5
    @8
    vy
    @0
    @4
    @7
    vx
    cC
    @0
    @3
    @6
    @1
    cA
    cB
    @2
    eceq2
    eqeq2d
    rexbidv
    abbidv
    vx
    vy
    cC
    cA
    df-qs
    vx
    vy
    cC
    cB
    df-qs
    3eqtr4g
end
