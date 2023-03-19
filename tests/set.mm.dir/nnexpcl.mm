include "cn.mm"
include "nnsscn.mm"
include "cv.mm"
include "nnmulcl.mm"
include "1nn.mm"
include "expcllem.mm"

theorem nnexpcl
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. NN /\ N e. NN0 ) -> ( A ^ N ) e. NN )

  proof
    vx
    vy
    cA
    cN
    cn
    nnsscn
    vx
    cv
    vy
    cv
    nnmulcl
    1nn
    expcllem
end
