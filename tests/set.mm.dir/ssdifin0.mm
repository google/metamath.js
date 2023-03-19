include "cdif.mm"
include "wss.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "ssrin.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "sseq0.mm"
include "sylancl.mm"

theorem ssdifin0
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A C_ ( B \ C ) -> ( A i^i C ) = (/) )

  proof
    cA
    cB
    cC
    cdif
    #
    wss
    cA
    cC
    cin
    #
    @0
    cC
    cin
    #
    wss
    @2
    c0
    wceq
    @1
    c0
    wceq
    cA
    @0
    cC
    ssrin
    @2
    cC
    @0
    cin
    c0
    @0
    cC
    incom
    cC
    cB
    disjdif
    eqtri
    @1
    @2
    sseq0
    sylancl
end
