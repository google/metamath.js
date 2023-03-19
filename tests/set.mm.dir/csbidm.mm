include "cvv.mm"
include "wcel.mm"
include "csb.mm"
include "wceq.mm"
include "csbnest1g.mm"
include "csbconstg.mm"
include "csbeq1d.mm"
include "eqtrd.mm"
include "wn.mm"
include "c0.mm"
include "csbprc.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem csbidm
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  assert |- [_ A / x ]_ [_ A / x ]_ B = [_ A / x ]_ B

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    vx
    cA
    cB
    csb
    #
    csb
    #
    @1
    wceq
    @0
    @2
    vx
    vx
    cA
    cA
    csb
    #
    cB
    csb
    @1
    vx
    cA
    cA
    cB
    cvv
    csbnest1g
    @0
    vx
    @3
    cA
    cB
    vx
    cA
    cA
    cvv
    csbconstg
    csbeq1d
    eqtrd
    @0
    wn
    @2
    c0
    @1
    vx
    cA
    @1
    csbprc
    vx
    cA
    cB
    csbprc
    eqtr4d
    pm2.61i
end
