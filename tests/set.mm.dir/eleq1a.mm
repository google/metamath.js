include "wceq.mm"
include "wcel.mm"
include "eleq1.mm"
include "biimprcd.mm"

theorem eleq1a
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. B -> ( C = A -> C e. B ) )

  proof
    cC
    cA
    wceq
    cC
    cB
    wcel
    cA
    cB
    wcel
    cC
    cA
    cB
    eleq1
    biimprcd
end
