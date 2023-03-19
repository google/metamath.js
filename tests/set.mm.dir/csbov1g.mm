include "wcel.mm"
include "co.mm"
include "csb.mm"
include "csbov12g.mm"
include "csbconstg.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem csbov1g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V

  disjoint C x
  disjoint F x
  assert |- ( A e. V -> [_ A / x ]_ ( B F C ) = ( [_ A / x ]_ B F C ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cB
    cC
    cF
    co
    csb
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cC
    csb
    #
    cF
    co
    @1
    cC
    cF
    co
    vx
    cA
    cB
    cC
    cF
    cV
    csbov12g
    @0
    @2
    cC
    @1
    cF
    vx
    cA
    cC
    cV
    csbconstg
    oveq2d
    eqtrd
end
