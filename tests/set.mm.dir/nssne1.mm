include "wss.mm"
include "wn.mm"
include "wne.mm"
include "wceq.mm"
include "sseq2.mm"
include "biimpcd.mm"
include "necon3bd.mm"
include "imp.mm"

theorem nssne1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ B /\ -. A C_ C ) -> B =/= C )

  proof
    cA
    cB
    wss
    #
    cA
    cC
    wss
    #
    wn
    cB
    cC
    wne
    @0
    @1
    cB
    cC
    cB
    cC
    wceq
    @0
    @1
    cB
    cC
    cA
    sseq2
    biimpcd
    necon3bd
    imp
end
