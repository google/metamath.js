include "cn.mm"
include "nnsscn.mm"
include "1nn.mm"
include "cv.mm"
include "nnmulcl.mm"
include "nnnn0addcl.mm"
include "risefaccllem.mm"

theorem nnrisefaccl
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. NN /\ N e. NN0 ) -> ( A RiseFac N ) e. NN )

  proof
    vx
    vy
    cA
    cn
    vk
    cN
    nnsscn
    1nn
    vx
    cv
    vy
    cv
    nnmulcl
    cA
    vk
    cv
    nnnn0addcl
    risefaccllem
end
