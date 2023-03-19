include "nfcv.mm"
include "inn0f.mm"

theorem inn0
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A i^i B ) =/= (/) <-> E. x e. A x e. B )

  proof
    vx
    cA
    cB
    vx
    cA
    nfcv
    vx
    cB
    nfcv
    inn0f
end
