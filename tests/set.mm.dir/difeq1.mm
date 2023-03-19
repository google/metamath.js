include "wceq.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "crab.mm"
include "cdif.mm"
include "rabeq.mm"
include "dfdif2.mm"
include "3eqtr4g.mm"

theorem difeq1
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A = B -> ( A \ C ) = ( B \ C ) )

  proof
    cA
    cB
    wceq
    vx
    cv
    cC
    wcel
    wn
    #
    vx
    cA
    crab
    @0
    vx
    cB
    crab
    cA
    cC
    cdif
    cB
    cC
    cdif
    @0
    vx
    cA
    cB
    rabeq
    vx
    cA
    cC
    dfdif2
    vx
    cB
    cC
    dfdif2
    3eqtr4g
end
