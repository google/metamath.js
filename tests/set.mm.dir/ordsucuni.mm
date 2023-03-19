include "word.mm"
include "con0.mm"
include "wss.mm"
include "cuni.mm"
include "csuc.mm"
include "ordsson.mm"
include "onsucuni.mm"
include "syl.mm"

theorem ordsucuni
  let cA: class A


  assert |- ( Ord A -> A C_ suc U. A )

  proof
    cA
    word
    cA
    con0
    wss
    cA
    cA
    cuni
    csuc
    wss
    cA
    ordsson
    cA
    onsucuni
    syl
end
