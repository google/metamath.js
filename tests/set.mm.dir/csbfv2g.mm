include "wcel.mm"
include "cfv.mm"
include "csb.mm"
include "csbfv12.mm"
include "csbconstg.mm"
include "fveq1d.mm"
include "syl5eq.mm"

theorem csbfv2g
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F

  disjoint F x
  assert |- ( A e. C -> [_ A / x ]_ ( F ` B ) = ( F ` [_ A / x ]_ B ) )

  proof
    cA
    cC
    wcel
    #
    vx
    cA
    cB
    cF
    cfv
    csb
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cF
    csb
    #
    cfv
    @1
    cF
    cfv
    vx
    cA
    cB
    cF
    csbfv12
    @0
    @1
    @2
    cF
    vx
    cA
    cF
    cC
    csbconstg
    fveq1d
    syl5eq
end
