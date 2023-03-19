include "wceq.mm"
include "wf1o.mm"
include "f1oeq2.mm"
include "f1oeq3.mm"
include "sylan9bb.mm"

theorem f1oeq23
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( A = B /\ C = D ) -> ( F : A -1-1-onto-> C <-> F : B -1-1-onto-> D ) )

  proof
    cA
    cB
    wceq
    cA
    cC
    cF
    wf1o
    cB
    cC
    cF
    wf1o
    cC
    cD
    wceq
    cB
    cD
    cF
    wf1o
    cA
    cB
    cC
    cF
    f1oeq2
    cC
    cD
    cB
    cF
    f1oeq3
    sylan9bb
end
