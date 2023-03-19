include "cr.mm"
include "ax-resscn.mm"
include "1re.mm"
include "cv.mm"
include "remulcl.mm"
include "cn0.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "nn0re.mm"
include "resubcl.mm"
include "sylan2.mm"
include "fallfaccllem.mm"

theorem refallfaccl
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. RR /\ N e. NN0 ) -> ( A FallFac N ) e. RR )

  proof
    vx
    vy
    cA
    cr
    vk
    cN
    ax-resscn
    1re
    vx
    cv
    vy
    cv
    remulcl
    vk
    cv
    #
    cn0
    wcel
    cA
    cr
    wcel
    @0
    cr
    wcel
    cA
    @0
    cmin
    co
    cr
    wcel
    @0
    nn0re
    cA
    @0
    resubcl
    sylan2
    fallfaccllem
end
