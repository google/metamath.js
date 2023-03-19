include "nfcv.mm"
include "neq0f.mm"

theorem neq0
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( -. A = (/) <-> E. x x e. A )

  proof
    vx
    cA
    vx
    cA
    nfcv
    neq0f
end
