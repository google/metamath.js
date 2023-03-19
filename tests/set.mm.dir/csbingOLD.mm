include "cv.mm"
include "cin.mm"
include "csb.mm"
include "wceq.mm"
include "csbeq1.mm"
include "ineq12d.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfcsb1v.mm"
include "nfin.mm"
include "csbeq1a.mm"
include "csbief.mm"
include "vtoclg.mm"

theorem csbingOLD
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vy: setvar y


  assert |- ( A e. B -> [_ A / x ]_ ( C i^i D ) = ( [_ A / x ]_ C i^i [_ A / x ]_ D ) )

  proof
    vx
    vy
    cv
    #
    cC
    cD
    cin
    #
    csb
    #
    vx
    @0
    cC
    csb
    #
    vx
    @0
    cD
    csb
    #
    cin
    #
    wceq
    vx
    cA
    @1
    csb
    #
    vx
    cA
    cC
    csb
    #
    vx
    cA
    cD
    csb
    #
    cin
    #
    wceq
    vy
    cA
    cB
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
    cC
    csbeq1
    vx
    @0
    cA
    cD
    csbeq1
    ineq12d
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
    cC
    nfcsb1v
    vx
    @0
    cD
    nfcsb1v
    nfin
    vx
    cv
    @0
    wceq
    cC
    @3
    cD
    @4
    vx
    @0
    cC
    csbeq1a
    vx
    @0
    cD
    csbeq1a
    ineq12d
    csbief
    vtoclg
end
