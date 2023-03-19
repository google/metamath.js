include "cv.mm"
include "ccom.mm"
include "csb.mm"
include "wceq.mm"
include "csbeq1.mm"
include "coeq12d.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfcsb1v.mm"
include "nfco.mm"
include "weq.mm"
include "csbeq1a.mm"
include "csbief.mm"
include "vtoclg.mm"

theorem csbcog
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vy: setvar y


  assert |- ( A e. V -> [_ A / x ]_ ( B o. C ) = ( [_ A / x ]_ B o. [_ A / x ]_ C ) )

  proof
    vx
    vy
    cv
    #
    cB
    cC
    ccom
    #
    csb
    #
    vx
    @0
    cB
    csb
    #
    vx
    @0
    cC
    csb
    #
    ccom
    #
    wceq
    vx
    cA
    @1
    csb
    #
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
    ccom
    #
    wceq
    vy
    cA
    cV
    @0
    cA
    wceq
    #
    @2
    @6
    @5
    @9
    vx
    @0
    cA
    @1
    csbeq1
    @10
    @3
    @7
    @4
    @8
    vx
    @0
    cA
    cB
    csbeq1
    vx
    @0
    cA
    cC
    csbeq1
    coeq12d
    eqeq12d
    vx
    @0
    @1
    @5
    vy
    vex
    vx
    @3
    @4
    vx
    @0
    cB
    nfcsb1v
    vx
    @0
    cC
    nfcsb1v
    nfco
    vx
    vy
    weq
    cB
    @3
    cC
    @4
    vx
    @0
    cB
    csbeq1a
    vx
    @0
    cC
    csbeq1a
    coeq12d
    csbief
    vtoclg
end
