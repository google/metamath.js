include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "sseq2.mm"
include "ss0.mm"
include "syl6bi.mm"
include "impcom.mm"

theorem sseq0
  let cA: class A
  let cB: class B


  assert |- ( ( A C_ B /\ B = (/) ) -> A = (/) )

  proof
    cB
    c0
    wceq
    #
    cA
    cB
    wss
    #
    cA
    c0
    wceq
    #
    @0
    @1
    cA
    c0
    wss
    @2
    cB
    c0
    cA
    sseq2
    cA
    ss0
    syl6bi
    impcom
end
