include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "wi.mm"
include "ax-1.mm"
include "wn.mm"
include "c0.mm"
include "fv2prc.mm"
include "eleq2d.mm"
include "noel.mm"
include "pm2.21i.mm"
include "syl6bi.mm"
include "pm2.61i.mm"

theorem elfv2ex
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F


  assert |- ( A e. ( ( F ` B ) ` C ) -> B e. _V )

  proof
    cB
    cvv
    wcel
    #
    cA
    cC
    cB
    cF
    cfv
    cfv
    #
    wcel
    #
    @0
    wi
    @0
    @2
    ax-1
    @0
    wn
    #
    @2
    cA
    c0
    wcel
    #
    @0
    @3
    @1
    c0
    cA
    cB
    cC
    cF
    fv2prc
    eleq2d
    @4
    @0
    cA
    noel
    pm2.21i
    syl6bi
    pm2.61i
end
