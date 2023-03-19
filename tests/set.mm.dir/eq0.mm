include "nfcv.mm"
include "eq0f.mm"

theorem eq0
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A = (/) <-> A. x -. x e. A )

  proof
    vx
    cA
    vx
    cA
    nfcv
    eq0f
end
