include "cr.mm"
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
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "secval.mm"
include "sylan.mm"
include "recoscl.mm"
include "1red.mm"
include "redivcl.mm"
include "syl3an1.mm"
include "syl3an2.mm"
include "3anidm12.mm"
include "eqeltrd.mm"

theorem reseccl
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ ( cos ` A ) =/= 0 ) -> ( sec ` A ) e. RR )

  proof
    cA
    cr
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
    cA
    csec
    cfv
    #
    c1
    @1
    cdiv
    co
    #
    cr
    @0
    cA
    cc
    wcel
    @2
    @3
    @4
    wceq
    cA
    recn
    cA
    secval
    sylan
    @0
    @2
    @4
    cr
    wcel
    #
    @0
    @0
    @1
    cr
    wcel
    #
    @2
    @5
    cA
    recoscl
    @0
    c1
    cr
    wcel
    @6
    @2
    @5
    @0
    1red
    c1
    @1
    redivcl
    syl3an1
    syl3an2
    3anidm12
    eqeltrd
end
