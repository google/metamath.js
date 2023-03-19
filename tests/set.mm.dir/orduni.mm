include "word.mm"
include "con0.mm"
include "wss.mm"
include "cuni.mm"
include "ordsson.mm"
include "ssorduni.mm"
include "syl.mm"

theorem orduni
  let cA: class A


  assert |- ( Ord A -> Ord U. A )

  proof
    cA
    word
    cA
    con0
    wss
    cA
    cuni
    word
    cA
    ordsson
    cA
    ssorduni
    syl
end
