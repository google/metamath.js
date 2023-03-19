include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "crab.mm"
include "cdif.mm"
include "eleq2.mm"
include "notbid.mm"
include "rabbidv.mm"
include "dfdif2.mm"
include "3eqtr4g.mm"

theorem difeq2
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A = B -> ( C \ A ) = ( C \ B ) )

  proof
    cA
    cB
    wceq
    #
    vx
    cv
    #
    cA
    wcel
    #
    wn
    #
    vx
    cC
    crab
    @1
    cB
    wcel
    #
    wn
    #
    vx
    cC
    crab
    cC
    cA
    cdif
    cC
    cB
    cdif
    @0
    @3
    @5
    vx
    cC
    @0
    @2
    @4
    cA
    cB
    @1
    eleq2
    notbid
    rabbidv
    vx
    cC
    cA
    dfdif2
    vx
    cC
    cB
    dfdif2
    3eqtr4g
end
