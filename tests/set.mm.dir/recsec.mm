include "cc.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "csec.mm"
include "cdiv.mm"
include "co.mm"
include "secval.mm"
include "oveq2d.mm"
include "wceq.mm"
include "coscl.mm"
include "recrec.mm"
include "sylan.mm"
include "eqtr2d.mm"

theorem recsec
  let cA: class A
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. CC /\ ( cos ` A ) =/= 0 ) -> ( cos ` A ) = ( 1 / ( sec ` A ) ) )

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
    c1
    cA
    csec
    cfv
    #
    cdiv
    co
    c1
    c1
    @1
    cdiv
    co
    #
    cdiv
    co
    #
    @1
    @3
    @4
    @5
    c1
    cdiv
    cA
    secval
    oveq2d
    @0
    @1
    cc
    wcel
    @2
    @6
    @1
    wceq
    cA
    coscl
    @1
    recrec
    sylan
    eqtr2d
end
