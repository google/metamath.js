include "c0.mm"
include "cin.mm"
include "incom.mm"
include "in0.mm"
include "eqtri.mm"

theorem 0in
  let cA: class A


  assert |- ( (/) i^i A ) = (/)

  proof
    c0
    cA
    cin
    cA
    c0
    cin
    c0
    c0
    cA
    incom
    cA
    in0
    eqtri
end
