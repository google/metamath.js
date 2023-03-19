include "cn0.mm"
include "nn0sscn.mm"
include "cv.mm"
include "nn0mulcl.mm"
include "1nn0.mm"
include "expcllem.mm"

theorem nn0expcl
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. NN0 /\ N e. NN0 ) -> ( A ^ N ) e. NN0 )

  proof
    vx
    vy
    cA
    cN
    cn0
    nn0sscn
    vx
    cv
    vy
    cv
    nn0mulcl
    1nn0
    expcllem
end
