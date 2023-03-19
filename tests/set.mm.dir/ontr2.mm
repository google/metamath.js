include "con0.mm"
include "wcel.mm"
include "word.mm"
include "wss.mm"
include "wa.mm"
include "wi.mm"
include "eloni.mm"
include "ordtr2.mm"
include "syl2an.mm"

theorem ontr2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. On /\ C e. On ) -> ( ( A C_ B /\ B e. C ) -> A e. C ) )

  proof
    cA
    con0
    wcel
    cA
    word
    cC
    word
    cA
    cB
    wss
    cB
    cC
    wcel
    wa
    cA
    cC
    wcel
    wi
    cC
    con0
    wcel
    cA
    eloni
    cC
    eloni
    cA
    cB
    cC
    ordtr2
    syl2an
end
