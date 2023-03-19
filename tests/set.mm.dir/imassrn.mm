include "cv.mm"
include "wcel.mm"
include "cop.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cima.mm"
include "crn.mm"
include "exsimpr.mm"
include "ss2abi.mm"
include "dfima3.mm"
include "dfrn3.mm"
include "3sstr4i.mm"

theorem imassrn
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( A " B ) C_ ran A

  proof
    vx
    cv
    #
    cB
    wcel
    #
    @0
    vy
    cv
    cop
    cA
    wcel
    #
    wa
    vx
    wex
    #
    vy
    cab
    @2
    vx
    wex
    #
    vy
    cab
    cA
    cB
    cima
    cA
    crn
    @3
    @4
    vy
    @1
    @2
    vx
    exsimpr
    ss2abi
    vx
    vy
    cA
    cB
    dfima3
    vx
    vy
    cA
    dfrn3
    3sstr4i
end
