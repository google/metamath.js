include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "crisefac.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cfz.mm"
include "cv.mm"
include "caddc.mm"
include "cprod.mm"
include "cn0.mm"
include "wceq.mm"
include "0nn0.mm"
include "risefacval.mm"
include "mpan2.mm"
include "c0.mm"
include "risefall0lem.mm"
include "prodeq1i.mm"
include "prod0.mm"
include "eqtri.mm"
include "syl6eq.mm"

theorem risefac0
  let cA: class A
  let vk: setvar k


  assert |- ( A e. CC -> ( A RiseFac 0 ) = 1 )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    crisefac
    co
    #
    cc0
    cc0
    c1
    cmin
    co
    cfz
    co
    #
    cA
    vk
    cv
    caddc
    co
    #
    vk
    cprod
    #
    c1
    @0
    cc0
    cn0
    wcel
    @1
    @4
    wceq
    0nn0
    cA
    vk
    cc0
    risefacval
    mpan2
    @4
    c0
    @3
    vk
    cprod
    c1
    @2
    c0
    @3
    vk
    risefall0lem
    prodeq1i
    @3
    vk
    prod0
    eqtri
    syl6eq
end
