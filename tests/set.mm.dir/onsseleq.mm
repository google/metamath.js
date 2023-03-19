include "con0.mm"
include "wcel.mm"
include "word.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "wb.mm"
include "eloni.mm"
include "ordsseleq.mm"
include "syl2an.mm"

theorem onsseleq
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> ( A e. B \/ A = B ) ) )

  proof
    cA
    con0
    wcel
    cA
    word
    cB
    word
    cA
    cB
    wss
    cA
    cB
    wcel
    cA
    cB
    wceq
    wo
    wb
    cB
    con0
    wcel
    cA
    eloni
    cB
    eloni
    cA
    cB
    ordsseleq
    syl2an
end
