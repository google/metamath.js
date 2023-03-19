include "cc.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "csec.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "secval.mm"
include "coscl.mm"
include "adantr.mm"
include "simpr.mm"
include "reccld.mm"
include "eqeltrd.mm"

theorem seccl
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ ( cos ` A ) =/= 0 ) -> ( sec ` A ) e. CC )

  proof
    cA
    cc
    wcel
    #
    cA
    ccos
    cfv
    #
    cc0
    wne
    #
    wa
    #
    cA
    csec
    cfv
    c1
    @1
    cdiv
    co
    cc
    cA
    secval
    @3
    @1
    @0
    @1
    cc
    wcel
    @2
    cA
    coscl
    adantr
    @0
    @2
    simpr
    reccld
    eqeltrd
end
