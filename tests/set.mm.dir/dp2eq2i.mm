include "wceq.mm"
include "cdp2.mm"
include "dp2eq2.mm"
include "ax-mp.mm"

theorem dp2eq2i
  let cA: class A
  let cB: class B
  let cC: class C
  assume dp2eq1i.1: |- A = B


  assert |- _ C A = _ C B

  proof
    cA
    cB
    wceq
    cC
    cA
    cdp2
    cC
    cB
    cdp2
    wceq
    dp2eq1i.1
    cA
    cB
    cC
    dp2eq2
    ax-mp
end
