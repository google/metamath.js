include "cr.mm"
include "ax-resscn.mm"
include "cv.mm"
include "remulcl.mm"
include "1re.mm"
include "expcllem.mm"

theorem reexpcl
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ N e. NN0 ) -> ( A ^ N ) e. RR )

  proof
    vx
    vy
    cA
    cN
    cr
    ax-resscn
    vx
    cv
    vy
    cv
    remulcl
    1re
    expcllem
end
