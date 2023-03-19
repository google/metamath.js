include "con0.mm"
include "wcel.mm"
include "word.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "eloni.mm"
include "ord0eln0.mm"
include "syl.mm"

theorem on0eln0
  let cA: class A


  assert |- ( A e. On -> ( (/) e. A <-> A =/= (/) ) )

  proof
    cA
    con0
    wcel
    cA
    word
    c0
    cA
    wcel
    cA
    c0
    wne
    wb
    cA
    eloni
    cA
    ord0eln0
    syl
end
