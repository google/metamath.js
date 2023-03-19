include "wcel.mm"
include "cin.mm"
include "cvv.mm"
include "incom.mm"
include "inex1g.mm"
include "syl5eqel.mm"

theorem inex2ALTV
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( B i^i A ) e. _V )

  proof
    cA
    cV
    wcel
    cB
    cA
    cin
    cA
    cB
    cin
    cvv
    cB
    cA
    incom
    cA
    cB
    cV
    inex1g
    syl5eqel
end
