include "wceq.mm"
include "cv.mm"
include "wss.mm"
include "cab.mm"
include "cpw.mm"
include "sseq2.mm"
include "abbidv.mm"
include "df-pw.mm"
include "3eqtr4g.mm"

theorem pweq
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A = B -> ~P A = ~P B )

  proof
    cA
    cB
    wceq
    #
    vx
    cv
    #
    cA
    wss
    #
    vx
    cab
    @1
    cB
    wss
    #
    vx
    cab
    cA
    cpw
    cB
    cpw
    @0
    @2
    @3
    vx
    cA
    cB
    @1
    sseq2
    abbidv
    vx
    cA
    df-pw
    vx
    cB
    df-pw
    3eqtr4g
end
