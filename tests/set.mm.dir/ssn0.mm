include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wceq.mm"
include "sseq0.mm"
include "ex.mm"
include "necon3d.mm"
include "imp.mm"

theorem ssn0
  let cA: class A
  let cB: class B


  assert |- ( ( A C_ B /\ A =/= (/) ) -> B =/= (/) )

  proof
    cA
    cB
    wss
    #
    cA
    c0
    wne
    cB
    c0
    wne
    @0
    cB
    c0
    cA
    c0
    @0
    cB
    c0
    wceq
    cA
    c0
    wceq
    cA
    cB
    sseq0
    ex
    necon3d
    imp
end
