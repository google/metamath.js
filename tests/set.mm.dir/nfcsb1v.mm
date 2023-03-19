include "nfcv.mm"
include "nfcsb1.mm"

theorem nfcsb1v
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- F/_ x [_ A / x ]_ B

  proof
    vx
    cA
    cB
    vx
    cA
    nfcv
    nfcsb1
end
