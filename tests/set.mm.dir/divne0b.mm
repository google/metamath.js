include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "diveq0.mm"
include "bicomd.mm"
include "necon3bid.mm"

theorem divne0b
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ B =/= 0 ) -> ( A =/= 0 <-> ( A / B ) =/= 0 ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cB
    cc0
    wne
    w3a
    #
    cA
    cc0
    cA
    cB
    cdiv
    co
    #
    cc0
    @0
    @1
    cc0
    wceq
    cA
    cc0
    wceq
    cA
    cB
    diveq0
    bicomd
    necon3bid
end
