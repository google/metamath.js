include "cmpt.mm"
include "nfmpt1.mm"
include "nfcv.mm"
include "nffv.mm"

theorem nffvmpt1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C

  disjoint C x
  assert |- F/_ x ( ( x e. A |-> B ) ` C )

  proof
    vx
    cC
    vx
    cA
    cB
    cmpt
    vx
    cA
    cB
    nfmpt1
    vx
    cC
    nfcv
    nffv
end
