include "cfv.mm"
include "wceq.mm"
include "cvv.mm"
include "wcel.mm"
include "wi.mm"
include "fvex.mm"
include "eleq1a.mm"
include "ax-mp.mm"
include "vprc.mm"
include "pm2.21i.mm"
include "syl.mm"
include "eqcoms.mm"

theorem fveqvfvv
  let cA: class A
  let cB: class B
  let cF: class F
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( F ` A ) = _V -> ( F ` A ) = B )

  proof
    cA
    cF
    cfv
    #
    cB
    wceq
    #
    cvv
    @0
    cvv
    @0
    wceq
    #
    cvv
    cvv
    wcel
    #
    @1
    @0
    cvv
    wcel
    @2
    @3
    wi
    cA
    cF
    fvex
    @0
    cvv
    cvv
    eleq1a
    ax-mp
    @3
    @1
    vprc
    pm2.21i
    syl
    eqcoms
end
