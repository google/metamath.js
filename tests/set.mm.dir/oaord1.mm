include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "coa.mm"
include "co.mm"
include "wb.mm"
include "wa.mm"
include "0elon.mm"
include "oaord.mm"
include "mp3an1.mm"
include "wceq.mm"
include "oa0.mm"
include "adantl.mm"
include "eleq1d.mm"
include "bitrd.mm"
include "ancoms.mm"

theorem oaord1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( (/) e. B <-> A e. ( A +o B ) ) )

  proof
    cB
    con0
    wcel
    #
    cA
    con0
    wcel
    #
    c0
    cB
    wcel
    #
    cA
    cA
    cB
    coa
    co
    #
    wcel
    #
    wb
    @0
    @1
    wa
    #
    @2
    cA
    c0
    coa
    co
    #
    @3
    wcel
    #
    @4
    c0
    con0
    wcel
    @0
    @1
    @2
    @7
    wb
    0elon
    c0
    cB
    cA
    oaord
    mp3an1
    @5
    @6
    cA
    @3
    @1
    @6
    cA
    wceq
    @0
    cA
    oa0
    adantl
    eleq1d
    bitrd
    ancoms
end
