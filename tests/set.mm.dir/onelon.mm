include "con0.mm"
include "wcel.mm"
include "word.mm"
include "eloni.mm"
include "ordelon.mm"
include "sylan.mm"

theorem onelon
  let cA: class A
  let cB: class B


  assert |- ( ( A e. On /\ B e. A ) -> B e. On )

  proof
    cA
    con0
    wcel
    cA
    word
    cB
    cA
    wcel
    cB
    con0
    wcel
    cA
    eloni
    cA
    cB
    ordelon
    sylan
end
