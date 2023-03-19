include "cvv.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "disj2.mm"
include "ddif.mm"
include "sseq2i.mm"
include "bitr2i.mm"

theorem ssindif0
  let cA: class A
  let cB: class B


  assert |- ( A C_ B <-> ( A i^i ( _V \ B ) ) = (/) )

  proof
    cA
    cvv
    cB
    cdif
    #
    cin
    c0
    wceq
    cA
    cvv
    @0
    cdif
    #
    wss
    cA
    cB
    wss
    cA
    @0
    disj2
    @1
    cB
    cA
    cB
    ddif
    sseq2i
    bitr2i
end
