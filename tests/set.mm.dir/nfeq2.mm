include "nfcv.mm"
include "nfeq.mm"

theorem nfeq2
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfeq2.1: |- F/_ x B

  disjoint A x
  assert |- F/ x A = B

  proof
    vx
    cA
    cB
    vx
    cA
    nfcv
    nfeq2.1
    nfeq
end
