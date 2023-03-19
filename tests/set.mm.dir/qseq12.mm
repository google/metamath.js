include "wceq.mm"
include "cqs.mm"
include "qseq1.mm"
include "qseq2.mm"
include "sylan9eq.mm"

theorem qseq12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A = B /\ C = D ) -> ( A /. C ) = ( B /. D ) )

  proof
    cA
    cB
    wceq
    cC
    cD
    wceq
    cA
    cC
    cqs
    cB
    cC
    cqs
    cB
    cD
    cqs
    cA
    cB
    cC
    qseq1
    cC
    cD
    cB
    qseq2
    sylan9eq
end
