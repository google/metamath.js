include "con0.mm"
include "wcel.mm"
include "word.mm"
include "wss.mm"
include "eloni.mm"
include "ordsson.mm"
include "syl.mm"

theorem onss
  let cA: class A


  assert |- ( A e. On -> A C_ On )

  proof
    cA
    con0
    wcel
    cA
    word
    cA
    con0
    wss
    cA
    eloni
    cA
    ordsson
    syl
end
