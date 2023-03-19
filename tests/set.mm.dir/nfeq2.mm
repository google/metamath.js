include "nfcv.mm"
include "nfeq.mm"

theorem nfeq2
  param vx: setvar x
  param cA: class A
  param cB: class B
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
