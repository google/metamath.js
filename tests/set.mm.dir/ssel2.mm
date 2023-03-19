include "wss.mm"
include "wcel.mm"
include "ssel.mm"
include "imp.mm"

theorem ssel2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ B /\ C e. A ) -> C e. B )

  proof
    cA
    cB
    wss
    cC
    cA
    wcel
    cC
    cB
    wcel
    cA
    cB
    cC
    ssel
    imp
end
