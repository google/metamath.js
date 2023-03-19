include "con0.mm"
include "wcel.mm"
include "word.mm"
include "wss.mm"
include "wne.mm"
include "wa.mm"
include "wb.mm"
include "eloni.mm"
include "ordelssne.mm"
include "syl2an.mm"

theorem onelpss
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( A e. B <-> ( A C_ B /\ A =/= B ) ) )

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
    wcel
    cA
    cB
    wss
    cA
    cB
    wne
    wa
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
    ordelssne
    syl2an
end
