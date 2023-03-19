include "nfcv.mm"
include "nfel.mm"

theorem nfel2
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfeq2.1: |- F/_ x B

  disjoint A x
  assert |- F/ x A e. B

  proof
    vx
    cA
    cB
    vx
    cA
    nfcv
    nfeq2.1
    nfel
end
