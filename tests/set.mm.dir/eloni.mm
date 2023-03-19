include "con0.mm"
include "wcel.mm"
include "word.mm"
include "elong.mm"
include "ibi.mm"

theorem eloni
  let cA: class A


  assert |- ( A e. On -> Ord A )

  proof
    cA
    con0
    wcel
    cA
    word
    cA
    con0
    elong
    ibi
end
