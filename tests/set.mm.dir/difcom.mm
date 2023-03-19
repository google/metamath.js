include "cun.mm"
include "wss.mm"
include "cdif.mm"
include "uncom.mm"
include "sseq2i.mm"
include "ssundif.mm"
include "3bitr3i.mm"

theorem difcom
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A \ B ) C_ C <-> ( A \ C ) C_ B )

  proof
    cA
    cB
    cC
    cun
    #
    wss
    cA
    cC
    cB
    cun
    #
    wss
    cA
    cB
    cdif
    cC
    wss
    cA
    cC
    cdif
    cB
    wss
    @0
    @1
    cA
    cB
    cC
    uncom
    sseq2i
    cA
    cB
    cC
    ssundif
    cA
    cC
    cB
    ssundif
    3bitr3i
end
