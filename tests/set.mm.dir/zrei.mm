include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "zre.mm"
include "ax-mp.mm"

theorem zrei
  let cA: class A
  assume zrei.1: |- A e. ZZ


  assert |- A e. RR

  proof
    cA
    cz
    wcel
    cA
    cr
    wcel
    zrei.1
    cA
    zre
    ax-mp
end
