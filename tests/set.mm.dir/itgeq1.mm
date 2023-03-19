include "nfcv.mm"
include "itgeq1f.mm"

theorem itgeq1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint A x
  disjoint B x
  assert |- ( A = B -> S. A C _d x = S. B C _d x )

  proof
    vx
    cA
    cB
    cC
    vx
    cA
    nfcv
    vx
    cB
    nfcv
    itgeq1f
end
