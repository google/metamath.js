include "wcel.mm"
include "co.mm"
include "csb.mm"
include "csbov12g.mm"
include "csbconstg.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem csbov2g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V

  disjoint B x
  disjoint F x
  assert |- ( A e. V -> [_ A / x ]_ ( B F C ) = ( B F [_ A / x ]_ C ) )

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
    cB
    @2
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
    @1
    cB
    @2
    cF
    vx
    cA
    cB
    cV
    csbconstg
    oveq1d
    eqtrd
end
