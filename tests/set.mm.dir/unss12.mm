include "wss.mm"
include "cun.mm"
include "unss1.mm"
include "unss2.mm"
include "sylan9ss.mm"

theorem unss12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A C_ B /\ C C_ D ) -> ( A u. C ) C_ ( B u. D ) )

  proof
    cA
    cB
    wss
    cC
    cD
    wss
    cA
    cC
    cun
    cB
    cC
    cun
    cB
    cD
    cun
    cA
    cB
    cC
    unss1
    cC
    cD
    cB
    unss2
    sylan9ss
end
