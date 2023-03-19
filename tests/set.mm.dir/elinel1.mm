include "cin.mm"
include "wcel.mm"
include "elin.mm"
include "simplbi.mm"

theorem elinel1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A e. ( B i^i C ) -> A e. B )

  proof
    cA
    cB
    cC
    cin
    wcel
    cA
    cB
    wcel
    cA
    cC
    wcel
    cA
    cB
    cC
    elin
    simplbi
end
