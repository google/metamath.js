include "cn0.mm"
include "nn0sscn.mm"
include "1nn0.mm"
include "cv.mm"
include "nn0mulcl.mm"
include "nn0addcl.mm"
include "risefaccllem.mm"

theorem nn0risefaccl
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. NN0 /\ N e. NN0 ) -> ( A RiseFac N ) e. NN0 )

  proof
    vx
    vy
    cA
    cn0
    vk
    cN
    nn0sscn
    1nn0
    vx
    cv
    vy
    cv
    nn0mulcl
    cA
    vk
    cv
    nn0addcl
    risefaccllem
end
