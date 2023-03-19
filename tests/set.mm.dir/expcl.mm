include "cc.mm"
include "ssid.mm"
include "cv.mm"
include "mulcl.mm"
include "ax-1cn.mm"
include "expcllem.mm"

theorem expcl
  let cA: class A
  let cN: class N
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. CC /\ N e. NN0 ) -> ( A ^ N ) e. CC )

  proof
    vx
    vy
    cA
    cN
    cc
    cc
    ssid
    vx
    cv
    vy
    cv
    mulcl
    ax-1cn
    expcllem
end
