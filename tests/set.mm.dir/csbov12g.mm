include "wcel.mm"
include "co.mm"
include "csb.mm"
include "csbov123.mm"
include "csbconstg.mm"
include "oveqd.mm"
include "syl5eq.mm"

theorem csbov12g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cV: class V

  disjoint F x
  assert |- ( A e. V -> [_ A / x ]_ ( B F C ) = ( [_ A / x ]_ B F [_ A / x ]_ C ) )

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
    vx
    cA
    cF
    csb
    #
    co
    @1
    @2
    cF
    co
    vx
    cA
    cB
    cC
    cF
    csbov123
    @0
    @3
    cF
    @1
    @2
    vx
    cA
    cF
    cV
    csbconstg
    oveqd
    syl5eq
end
