include "cin.mm"
include "cvv.mm"
include "incom.mm"
include "inex1.mm"
include "eqeltri.mm"

theorem inex2
  let cA: class A
  let cB: class B
  assume inex2.1: |- A e. _V


  assert |- ( B i^i A ) e. _V

  proof
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
    inex2.1
    inex1
    eqeltri
end
