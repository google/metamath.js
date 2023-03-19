include "cz.mm"
include "zsscn.mm"
include "1z.mm"
include "cv.mm"
include "zmulcl.mm"
include "cn0.mm"
include "wcel.mm"
include "caddc.mm"
include "co.mm"
include "nn0z.mm"
include "zaddcl.mm"
include "sylan2.mm"
include "risefaccllem.mm"

theorem zrisefaccl
  let cA: class A
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. ZZ /\ N e. NN0 ) -> ( A RiseFac N ) e. ZZ )

  proof
    vx
    vy
    cA
    cz
    vk
    cN
    zsscn
    1z
    vx
    cv
    vy
    cv
    zmulcl
    vk
    cv
    #
    cn0
    wcel
    cA
    cz
    wcel
    @0
    cz
    wcel
    cA
    @0
    caddc
    co
    cz
    wcel
    @0
    nn0z
    cA
    @0
    zaddcl
    sylan2
    risefaccllem
end
