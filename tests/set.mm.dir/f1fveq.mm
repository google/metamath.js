include "wf1.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "wceq.mm"
include "f1veqaeq.mm"
include "fveq2.mm"
include "impbid1.mm"

theorem f1fveq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F


  assert |- ( ( F : A -1-1-> B /\ ( C e. A /\ D e. A ) ) -> ( ( F ` C ) = ( F ` D ) <-> C = D ) )

  proof
    cA
    cB
    cF
    wf1
    cC
    cA
    wcel
    cD
    cA
    wcel
    wa
    wa
    cC
    cF
    cfv
    cD
    cF
    cfv
    wceq
    cC
    cD
    wceq
    cA
    cB
    cC
    cD
    cF
    f1veqaeq
    cC
    cD
    cF
    fveq2
    impbid1
end
