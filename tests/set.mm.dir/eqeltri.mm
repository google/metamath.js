include "wcel.mm"
include "eleq1i.mm"
include "mpbir.mm"

theorem eqeltri
  param cA: class A
  param cB: class B
  param cC: class C
  assume eqeltr.1: |- A = B
  assume eqeltr.2: |- B e. C


  assert |- A e. C

  proof
    cA
    cC
    wcel
    cB
    cC
    wcel
    eqeltr.2
    cA
    cB
    cC
    eqeltr.1
    eleq1i
    mpbir
end
