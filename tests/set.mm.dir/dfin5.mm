include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cab.mm"
include "crab.mm"
include "df-in.mm"
include "df-rab.mm"
include "eqtr4i.mm"

theorem dfin5
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( A i^i B ) = { x e. A | x e. B }

  proof
    cA
    cB
    cin
    vx
    cv
    #
    cA
    wcel
    @0
    cB
    wcel
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
    df-in
    @1
    vx
    cA
    df-rab
    eqtr4i
end
