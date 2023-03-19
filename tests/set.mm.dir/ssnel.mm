include "wss.mm"
include "wcel.mm"
include "ssel2.mm"
include "stoic1a.mm"

theorem ssnel
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ B /\ -. C e. B ) -> -. C e. A )

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
    ssel2
    stoic1a
end
