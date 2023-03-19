include "wceq.mm"
include "cneg.mm"
include "negeq.mm"
include "ax-mp.mm"

theorem negeqi
  let cA: class A
  let cB: class B
  assume negeqi.1: |- A = B


  assert |- -u A = -u B

  proof
    cA
    cB
    wceq
    cA
    cneg
    cB
    cneg
    wceq
    negeqi.1
    cA
    cB
    negeq
    ax-mp
end
