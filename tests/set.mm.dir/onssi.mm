include "con0.mm"
include "wcel.mm"
include "wss.mm"
include "onss.mm"
include "ax-mp.mm"

theorem onssi
  let cA: class A
  assume onssi.1: |- A e. On


  assert |- A C_ On

  proof
    cA
    con0
    wcel
    cA
    con0
    wss
    onssi.1
    cA
    onss
    ax-mp
end
