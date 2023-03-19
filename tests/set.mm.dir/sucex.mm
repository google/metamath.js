include "cvv.mm"
include "wcel.mm"
include "csuc.mm"
include "sucexg.mm"
include "ax-mp.mm"

theorem sucex
  let cA: class A
  assume sucex.1: |- A e. _V


  assert |- suc A e. _V

  proof
    cA
    cvv
    wcel
    cA
    csuc
    cvv
    wcel
    sucex.1
    cA
    cvv
    sucexg
    ax-mp
end
