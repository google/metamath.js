include "con0.mm"
include "wcel.mm"
include "word.mm"
include "wss.mm"
include "wn.mm"
include "wb.mm"
include "eloni.mm"
include "ordtri1.mm"
include "syl2an.mm"

theorem ontri1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. On ) -> ( A C_ B <-> -. B e. A ) )

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
    cB
    cA
    wcel
    wn
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
    ordtri1
    syl2an
end
