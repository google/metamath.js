include "word.mm"
include "wtr.mm"
include "cuni.mm"
include "wss.mm"
include "ordtr.mm"
include "df-tr.mm"
include "sylib.mm"

theorem orduniss
  let cA: class A


  assert |- ( Ord A -> U. A C_ A )

  proof
    cA
    word
    cA
    wtr
    cA
    cuni
    cA
    wss
    cA
    ordtr
    cA
    df-tr
    sylib
end
