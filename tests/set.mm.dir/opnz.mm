include "cop.mm"
include "c0.mm"
include "wne.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "opprc.mm"
include "necon1ai.mm"
include "csn.mm"
include "cpr.mm"
include "dfopg.mm"
include "snex.mm"
include "prnz.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "impbii.mm"

theorem opnz
  let cA: class A
  let cB: class B


  assert |- ( <. A , B >. =/= (/) <-> ( A e. _V /\ B e. _V ) )

  proof
    cA
    cB
    cop
    #
    c0
    wne
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    wa
    #
    @1
    @0
    c0
    cA
    cB
    opprc
    necon1ai
    @1
    @0
    cA
    csn
    #
    cA
    cB
    cpr
    #
    cpr
    #
    c0
    cA
    cB
    cvv
    cvv
    dfopg
    @4
    c0
    wne
    @1
    @2
    @3
    cA
    snex
    prnz
    a1i
    eqnetrd
    impbii
end
