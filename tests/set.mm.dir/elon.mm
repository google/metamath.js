include "cvv.mm"
include "wcel.mm"
include "con0.mm"
include "word.mm"
include "wb.mm"
include "elong.mm"
include "ax-mp.mm"

theorem elon
  let cA: class A
  assume elon.1: |- A e. _V


  assert |- ( A e. On <-> Ord A )

  proof
    cA
    cvv
    wcel
    cA
    con0
    wcel
    cA
    word
    wb
    elon.1
    cA
    cvv
    elong
    ax-mp
end
