include "cen.mm"
include "wbr.mm"
include "ensym.mm"
include "ax-mp.mm"

theorem ensymi
  let cA: class A
  let cB: class B
  assume ensymi.2: |- A ~~ B


  assert |- B ~~ A

  proof
    cA
    cB
    cen
    wbr
    cB
    cA
    cen
    wbr
    ensymi.2
    cA
    cB
    ensym
    ax-mp
end
