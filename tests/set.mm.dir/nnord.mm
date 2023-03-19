include "com.mm"
include "wcel.mm"
include "con0.mm"
include "word.mm"
include "nnon.mm"
include "eloni.mm"
include "syl.mm"

theorem nnord
  let cA: class A


  assert |- ( A e. _om -> Ord A )

  proof
    cA
    com
    wcel
    cA
    con0
    wcel
    cA
    word
    cA
    nnon
    cA
    eloni
    syl
end
