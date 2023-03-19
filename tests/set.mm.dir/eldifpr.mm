include "wcel.mm"
include "cpr.mm"
include "wn.mm"
include "wa.mm"
include "wne.mm"
include "cdif.mm"
include "w3a.mm"
include "wceq.mm"
include "wo.mm"
include "elprg.mm"
include "notbid.mm"
include "neanior.mm"
include "syl6bbr.mm"
include "pm5.32i.mm"
include "eldif.mm"
include "3anass.mm"
include "3bitr4i.mm"

theorem eldifpr
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( A e. ( B \ { C , D } ) <-> ( A e. B /\ A =/= C /\ A =/= D ) )

  proof
    cA
    cB
    wcel
    #
    cA
    cC
    cD
    cpr
    #
    wcel
    #
    wn
    #
    wa
    @0
    cA
    cC
    wne
    #
    cA
    cD
    wne
    #
    wa
    #
    wa
    cA
    cB
    @1
    cdif
    wcel
    @0
    @4
    @5
    w3a
    @0
    @3
    @6
    @0
    @3
    cA
    cC
    wceq
    cA
    cD
    wceq
    wo
    #
    wn
    @6
    @0
    @2
    @7
    cA
    cC
    cD
    cB
    elprg
    notbid
    cA
    cC
    cA
    cD
    neanior
    syl6bbr
    pm5.32i
    cA
    cB
    @1
    eldif
    @0
    @4
    @5
    3anass
    3bitr4i
end
