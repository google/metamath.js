include "wss.mm"
include "wne.mm"
include "cdif.mm"
include "c0.mm"
include "wceq.mm"
include "ssdif0.mm"
include "eqss.mm"
include "simplbi2.mm"
include "syl5bir.mm"
include "necon3d.mm"
include "imp.mm"

theorem pssdifn0
  let cA: class A
  let cB: class B


  assert |- ( ( A C_ B /\ A =/= B ) -> ( B \ A ) =/= (/) )

  proof
    cA
    cB
    wss
    #
    cA
    cB
    wne
    cB
    cA
    cdif
    #
    c0
    wne
    @0
    @1
    c0
    cA
    cB
    @1
    c0
    wceq
    cB
    cA
    wss
    #
    @0
    cA
    cB
    wceq
    #
    cB
    cA
    ssdif0
    @3
    @0
    @2
    cA
    cB
    eqss
    simplbi2
    syl5bir
    necon3d
    imp
end
