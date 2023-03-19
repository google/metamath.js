include "wss.mm"
include "cun.mm"
include "ssun3.mm"
include "ssun4.mm"
include "jaoi.mm"

theorem ssun
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ B \/ A C_ C ) -> A C_ ( B u. C ) )

  proof
    cA
    cB
    wss
    cA
    cB
    cC
    cun
    wss
    cA
    cC
    wss
    cA
    cB
    cC
    ssun3
    cA
    cC
    cB
    ssun4
    jaoi
end
