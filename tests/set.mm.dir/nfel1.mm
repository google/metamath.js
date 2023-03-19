include "nfcv.mm"
include "nfel.mm"

theorem nfel1
  let vx: setvar x
  let cA: class A
  let cB: class B
  assume nfeq1.1: |- F/_ x A

  disjoint B x
  assert |- F/ x A e. B

  proof
    vx
    cA
    cB
    nfeq1.1
    vx
    cB
    nfcv
    nfel
end
