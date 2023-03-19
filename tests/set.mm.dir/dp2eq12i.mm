include "cdp2.mm"
include "dp2eq1i.mm"
include "dp2eq2i.mm"
include "eqtri.mm"

theorem dp2eq12i
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume dp2eq1i.1: |- A = B
  assume dp2eq12i.2: |- C = D


  assert |- _ A C = _ B D

  proof
    cA
    cC
    cdp2
    cB
    cC
    cdp2
    cB
    cD
    cdp2
    cA
    cB
    cC
    dp2eq1i.1
    dp2eq1i
    cC
    cD
    cB
    dp2eq12i.2
    dp2eq2i
    eqtri
end
