include "con0.mm"
include "wcel.mm"
include "word.mm"
include "wa.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "csuc.mm"
include "wb.mm"
include "eloni.mm"
include "ordsseleq.mm"
include "sylan.mm"
include "elsucg.mm"
include "adantr.mm"
include "bitr4d.mm"

theorem ordsssuc
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ Ord B ) -> ( A C_ B <-> A e. suc B ) )

  proof
    cA
    con0
    wcel
    #
    cB
    word
    #
    wa
    cA
    cB
    wss
    #
    cA
    cB
    wcel
    cA
    cB
    wceq
    wo
    #
    cA
    cB
    csuc
    wcel
    #
    @0
    cA
    word
    @1
    @2
    @3
    wb
    cA
    eloni
    cA
    cB
    ordsseleq
    sylan
    @0
    @4
    @3
    wb
    @1
    cA
    cB
    con0
    elsucg
    adantr
    bitr4d
end
