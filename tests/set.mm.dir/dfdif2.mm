include "cdif.mm"
include "cv.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "df-dif.mm"
include "df-rab.mm"
include "eqtr4i.mm"

theorem dfdif2
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A \ B ) = { x e. A | -. x e. B }

  proof
    cA
    cB
    cdif
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
    wn
    #
    wa
    vx
    cab
    @1
    vx
    cA
    crab
    vx
    cA
    cB
    df-dif
    @1
    vx
    cA
    df-rab
    eqtr4i
end
