include "cin.mm"
include "incom.mm"
include "inss1.mm"
include "eqsstr3i.mm"

theorem inss2
  let cA: class A
  let cB: class B


  assert |- ( A i^i B ) C_ B

  proof
    cA
    cB
    cin
    cB
    cA
    cin
    cB
    cB
    cA
    incom
    cB
    cA
    inss1
    eqsstr3i
end
