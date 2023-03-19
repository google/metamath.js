include "cc.mm"
include "ssid.mm"
include "ax-1cn.mm"
include "cv.mm"
include "mulcl.mm"
include "cn0.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "nn0cn.mm"
include "subcl.mm"
include "sylan2.mm"
include "fallfaccllem.mm"

theorem fallfaccl
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. CC /\ N e. NN0 ) -> ( A FallFac N ) e. CC )

  proof
    vx
    vy
    cA
    cc
    vk
    cN
    cc
    ssid
    ax-1cn
    vx
    cv
    vy
    cv
    mulcl
    vk
    cv
    #
    cn0
    wcel
    cA
    cc
    wcel
    @0
    cc
    wcel
    cA
    @0
    cmin
    co
    cc
    wcel
    @0
    nn0cn
    cA
    @0
    subcl
    sylan2
    fallfaccllem
end
