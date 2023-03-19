include "con0.mm"
include "wcel.mm"
include "word.mm"
include "wss.mm"
include "csuc.mm"
include "wb.mm"
include "eloni.mm"
include "ordsssuc.mm"
include "sylan2.mm"

theorem onsssuc
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> A e. suc B ) )

  proof
    cB
    con0
    wcel
    cA
    con0
    wcel
    cB
    word
    cA
    cB
    wss
    cA
    cB
    csuc
    wcel
    wb
    cB
    eloni
    cA
    cB
    ordsssuc
    sylan2
end
