include "wcel.mm"
include "eleq1i.mm"
include "mtbir.mm"

theorem eqneltri
  let cA: class A
  let cB: class B
  let cC: class C
  assume eqneltri.1: |- A = B
  assume eqneltri.2: |- -. B e. C


  assert |- -. A e. C

  proof
    cA
    cC
    wcel
    cB
    cC
    wcel
    eqneltri.2
    cA
    cB
    cC
    eqneltri.1
    eleq1i
    mtbir
end
