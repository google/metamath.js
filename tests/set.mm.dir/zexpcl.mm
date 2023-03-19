include "cz.mm"
include "zsscn.mm"
include "cv.mm"
include "zmulcl.mm"
include "1z.mm"
include "expcllem.mm"

theorem zexpcl
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. ZZ /\ N e. NN0 ) -> ( A ^ N ) e. ZZ )

  proof
    vx
    vy
    cA
    cN
    cz
    zsscn
    vx
    cv
    vy
    cv
    zmulcl
    1z
    expcllem
end
