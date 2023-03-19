include "cv.mm"
include "wceq.mm"
include "wsbc.mm"
include "dfsbcq.mm"
include "eqeq1.mm"
include "wsb.mm"
include "sbsbc.mm"
include "eqsb3.mm"
include "bitr3i.mm"
include "vtoclbg.mm"

theorem eqsbc3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V
  let vy: setvar y

  disjoint B x
  disjoint x y
  disjoint B y
  disjoint A y
  assert |- ( A e. V -> ( [. A / x ]. x = B <-> A = B ) )

  proof
    vx
    cv
    cB
    wceq
    #
    vx
    vy
    cv
    #
    wsbc
    #
    @1
    cB
    wceq
    #
    @0
    vx
    cA
    wsbc
    cA
    cB
    wceq
    vy
    cA
    cV
    @0
    vx
    @1
    cA
    dfsbcq
    @1
    cA
    cB
    eqeq1
    @2
    @0
    vx
    vy
    wsb
    @3
    @0
    vx
    vy
    sbsbc
    vy
    vx
    cB
    eqsb3
    bitr3i
    vtoclbg
end
