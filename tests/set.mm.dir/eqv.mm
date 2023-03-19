include "nfcv.mm"
include "eqvf.mm"

theorem eqv
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A = _V <-> A. x x e. A )

  proof
    vx
    cA
    vx
    cA
    nfcv
    eqvf
end
