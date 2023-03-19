include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "suceloni.mm"
include "ax-mp.mm"

theorem onsuci
  let cA: class A
  assume onssi.1: |- A e. On


  assert |- suc A e. On

  proof
    cA
    con0
    wcel
    cA
    csuc
    con0
    wcel
    onssi.1
    cA
    suceloni
    ax-mp
end
