include "wceq.mm"
include "wf.mm"
include "feq2.mm"
include "feq3.mm"
include "sylan9bb.mm"

theorem feq23
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( A = C /\ B = D ) -> ( F : A --> B <-> F : C --> D ) )

  proof
    cA
    cC
    wceq
    cA
    cB
    cF
    wf
    cC
    cB
    cF
    wf
    cB
    cD
    wceq
    cC
    cD
    cF
    wf
    cA
    cC
    cB
    cF
    feq2
    cB
    cD
    cC
    cF
    feq3
    sylan9bb
end
