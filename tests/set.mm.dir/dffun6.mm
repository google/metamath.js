include "nfcv.mm"
include "dffun6f.mm"

theorem dffun6
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cA: class A

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint A x
  disjoint A y
  assert |- ( Fun F <-> ( Rel F /\ A. x E* y x F y ) )

  proof
    vx
    vy
    cF
    vx
    cF
    nfcv
    vy
    cF
    nfcv
    dffun6f
end
