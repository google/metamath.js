include "wss.mm"
include "wn.mm"
include "wne.mm"
include "wceq.mm"
include "sseq1.mm"
include "biimpcd.mm"
include "necon3bd.mm"
include "imp.mm"

theorem nssne2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A C_ C /\ -. B C_ C ) -> A =/= B )

  proof
    cA
    cC
    wss
    #
    cB
    cC
    wss
    #
    wn
    cA
    cB
    wne
    @0
    @1
    cA
    cB
    cA
    cB
    wceq
    @0
    @1
    cA
    cB
    cC
    sseq1
    biimpcd
    necon3bd
    imp
end
