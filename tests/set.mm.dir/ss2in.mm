include "wss.mm"
include "cin.mm"
include "ssrin.mm"
include "sslin.mm"
include "sylan9ss.mm"

theorem ss2in
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A C_ B /\ C C_ D ) -> ( A i^i C ) C_ ( B i^i D ) )

  proof
    cA
    cB
    wss
    cC
    cD
    wss
    cA
    cC
    cin
    cB
    cC
    cin
    cB
    cD
    cin
    cA
    cB
    cC
    ssrin
    cC
    cD
    cB
    sslin
    sylan9ss
end
