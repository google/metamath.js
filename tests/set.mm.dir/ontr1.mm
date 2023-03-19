include "con0.mm"
include "wcel.mm"
include "word.mm"
include "wa.mm"
include "wi.mm"
include "eloni.mm"
include "ordtr1.mm"
include "syl.mm"

theorem ontr1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( C e. On -> ( ( A e. B /\ B e. C ) -> A e. C ) )

  proof
    cC
    con0
    wcel
    cC
    word
    cA
    cB
    wcel
    cB
    cC
    wcel
    wa
    cA
    cC
    wcel
    wi
    cC
    eloni
    cA
    cB
    cC
    ordtr1
    syl
end
