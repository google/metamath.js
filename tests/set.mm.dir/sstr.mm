include "wss.mm"
include "sstr2.mm"
include "imp.mm"

theorem sstr
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ B /\ B C_ C ) -> A C_ C )

  proof
    cA
    cB
    wss
    cB
    cC
    wss
    cA
    cC
    wss
    cA
    cB
    cC
    sstr2
    imp
end
