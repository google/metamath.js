include "con0.mm"
include "wcel.mm"
include "word.mm"
include "eloni.mm"
include "ax-mp.mm"

theorem onordi
  let cA: class A
  assume on.1: |- A e. On


  assert |- Ord A

  proof
    cA
    con0
    wcel
    cA
    word
    on.1
    cA
    eloni
    ax-mp
end
