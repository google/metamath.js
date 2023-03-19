include "nfcv.mm"
include "n0f.mm"

theorem n0
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A =/= (/) <-> E. x x e. A )

  proof
    vx
    cA
    vx
    cA
    nfcv
    n0f
end
