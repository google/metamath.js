include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wsbc.mm"
include "cab.mm"
include "csb.mm"
include "dfsbcq.mm"
include "abbidv.mm"
include "df-csb.mm"
include "3eqtr4g.mm"

theorem csbeq1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- ( A = B -> [_ A / x ]_ C = [_ B / x ]_ C )

  proof
    cA
    cB
    wceq
    #
    vy
    cv
    cC
    wcel
    #
    vx
    cA
    wsbc
    #
    vy
    cab
    @1
    vx
    cB
    wsbc
    #
    vy
    cab
    vx
    cA
    cC
    csb
    vx
    cB
    cC
    csb
    @0
    @2
    @3
    vy
    @1
    vx
    cA
    cB
    dfsbcq
    abbidv
    vx
    vy
    cA
    cC
    df-csb
    vx
    vy
    cB
    cC
    df-csb
    3eqtr4g
end
