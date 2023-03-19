include "nfcv.mm"
include "nfeq.mm"

theorem nfeq1
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfeq1.1: |- F/_ x A

  disjoint B x
  assert |- F/ x A = B

  proof
    vx
    cA
    cB
    nfeq1.1
    vx
    cB
    nfcv
    nfeq
end
