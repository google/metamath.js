include "cq.mm"
include "qsscn.mm"
include "cv.mm"
include "qmulcl.mm"
include "c1.mm"
include "cz.mm"
include "wcel.mm"
include "1z.mm"
include "zq.mm"
include "ax-mp.mm"
include "expcllem.mm"

theorem qexpcl
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. QQ /\ N e. NN0 ) -> ( A ^ N ) e. QQ )

  proof
    vx
    vy
    cA
    cN
    cq
    qsscn
    vx
    cv
    vy
    cv
    qmulcl
    c1
    cz
    wcel
    c1
    cq
    wcel
    1z
    c1
    zq
    ax-mp
    expcllem
end
