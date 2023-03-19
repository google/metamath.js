include "cat.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "wceq.mm"
include "c0h.mm"
include "wne.mm"
include "atne0.mm"
include "ad2antrr.mm"
include "wo.mm"
include "cch.mm"
include "wi.mm"
include "atelch.mm"
include "atss.mm"
include "sylan.mm"
include "imp.mm"
include "ord.mm"
include "necon1ad.mm"
include "mpd.mm"
include "ex.mm"
include "eqimss.mm"
include "impbid1.mm"

theorem atsseq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. HAtoms /\ B e. HAtoms ) -> ( A C_ B <-> A = B ) )

  proof
    cA
    cat
    wcel
    #
    cB
    cat
    wcel
    #
    wa
    #
    cA
    cB
    wss
    #
    cA
    cB
    wceq
    #
    @2
    @3
    @4
    @2
    @3
    wa
    #
    cA
    c0h
    wne
    #
    @4
    @0
    @6
    @1
    @3
    cA
    atne0
    ad2antrr
    @5
    @4
    cA
    c0h
    @5
    @4
    cA
    c0h
    wceq
    #
    @2
    @3
    @4
    @7
    wo
    #
    @0
    cA
    cch
    wcel
    @1
    @3
    @8
    wi
    cA
    atelch
    cA
    cB
    atss
    sylan
    imp
    ord
    necon1ad
    mpd
    ex
    cA
    cB
    eqimss
    impbid1
end
