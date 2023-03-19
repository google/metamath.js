include "wceq.mm"
include "wss.mm"
include "sseq1.mm"
include "sseq2.mm"
include "sylan9bb.mm"

theorem sseq12
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A = B /\ C = D ) -> ( A C_ C <-> B C_ D ) )

  proof
    cA
    cB
    wceq
    cA
    cC
    wss
    cB
    cC
    wss
    cC
    cD
    wceq
    cB
    cD
    wss
    cA
    cB
    cC
    sseq1
    cC
    cD
    cB
    sseq2
    sylan9bb
end
