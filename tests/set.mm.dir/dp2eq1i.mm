include "wceq.mm"
include "cdp2.mm"
include "dp2eq1.mm"
include "ax-mp.mm"

theorem dp2eq1i
  let cA: class A
  let cB: class B
  let cC: class C
  assume dp2eq1i.1: |- A = B


  assert |- _ A C = _ B C

  proof
    cA
    cB
    wceq
    cA
    cC
    cdp2
    cB
    cC
    cdp2
    wceq
    dp2eq1i.1
    cA
    cB
    cC
    dp2eq1
    ax-mp
end
