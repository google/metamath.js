include "cr.mm"
include "ax-resscn.mm"
include "cv.mm"
include "remulcl.mm"
include "1re.mm"
include "rereccl.mm"
include "expcl2lem.mm"

theorem reexpclz
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ A =/= 0 /\ N e. ZZ ) -> ( A ^ N ) e. RR )

  proof
    vx
    vy
    cA
    cN
    cr
    ax-resscn
    vx
    cv
    #
    vy
    cv
    remulcl
    1re
    @0
    rereccl
    expcl2lem
end
