include "cvv.mm"
include "wcel.mm"
include "cen.mm"
include "wbr.mm"
include "enrefg.mm"
include "ax-mp.mm"

theorem enref
  let cA: class A
  assume enref.1: |- A e. _V


  assert |- A ~~ A

  proof
    cA
    cvv
    wcel
    cA
    cA
    cen
    wbr
    enref.1
    cA
    cvv
    enrefg
    ax-mp
end
