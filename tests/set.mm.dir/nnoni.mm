include "com.mm"
include "wcel.mm"
include "con0.mm"
include "nnon.mm"
include "ax-mp.mm"

theorem nnoni
  let cA: class A
  assume nnoni.1: |- A e. _om


  assert |- A e. On

  proof
    cA
    com
    wcel
    cA
    con0
    wcel
    nnoni.1
    cA
    nnon
    ax-mp
end
