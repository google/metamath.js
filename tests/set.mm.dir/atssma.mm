include "cat.mm"
include "wcel.mm"
include "cch.mm"
include "wa.mm"
include "wss.mm"
include "cin.mm"
include "wi.mm"
include "wceq.mm"
include "df-ss.mm"
include "biimpi.mm"
include "eleq1d.mm"
include "biimprcd.mm"
include "adantr.mm"
include "c0h.mm"
include "wn.mm"
include "incom.mm"
include "eleq1i.mm"
include "atne0.mm"
include "neneqd.mm"
include "sylbi.mm"
include "wb.mm"
include "atnssm0.mm"
include "ancoms.mm"
include "biimpd.mm"
include "con1d.mm"
include "syl5.mm"
include "impbid.mm"

theorem atssma
  let cA: class A
  let cB: class B


  assert |- ( ( A e. HAtoms /\ B e. CH ) -> ( A C_ B <-> ( A i^i B ) e. HAtoms ) )

  proof
    cA
    cat
    wcel
    #
    cB
    cch
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
    cin
    #
    cat
    wcel
    #
    @0
    @3
    @5
    wi
    @1
    @3
    @5
    @0
    @3
    @4
    cA
    cat
    @3
    @4
    cA
    wceq
    cA
    cB
    df-ss
    biimpi
    eleq1d
    biimprcd
    adantr
    @5
    cB
    cA
    cin
    #
    c0h
    wceq
    #
    wn
    #
    @2
    @3
    @5
    @6
    cat
    wcel
    #
    @8
    @4
    @6
    cat
    cA
    cB
    incom
    eleq1i
    @9
    @6
    c0h
    @6
    atne0
    neneqd
    sylbi
    @2
    @3
    @7
    @2
    @3
    wn
    #
    @7
    @1
    @0
    @10
    @7
    wb
    cB
    cA
    atnssm0
    ancoms
    biimpd
    con1d
    syl5
    impbid
end
