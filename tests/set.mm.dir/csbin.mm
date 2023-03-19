include "cvv.mm"
include "wcel.mm"
include "cin.mm"
include "csb.mm"
include "wceq.mm"
include "cv.mm"
include "csbeq1.mm"
include "ineq12d.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfcsb1v.mm"
include "nfin.mm"
include "weq.mm"
include "csbeq1a.mm"
include "csbief.mm"
include "vtoclg.mm"
include "wn.mm"
include "c0.mm"
include "csbprc.mm"
include "in0.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "pm2.61i.mm"

theorem csbin
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- [_ A / x ]_ ( B i^i C ) = ( [_ A / x ]_ B i^i [_ A / x ]_ C )

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    cB
    cC
    cin
    #
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
    cin
    #
    wceq
    #
    vx
    vy
    cv
    #
    @1
    csb
    #
    vx
    @7
    cB
    csb
    #
    vx
    @7
    cC
    csb
    #
    cin
    #
    wceq
    @6
    vy
    cA
    cvv
    @7
    cA
    wceq
    #
    @8
    @2
    @11
    @5
    vx
    @7
    cA
    @1
    csbeq1
    @12
    @9
    @3
    @10
    @4
    vx
    @7
    cA
    cB
    csbeq1
    vx
    @7
    cA
    cC
    csbeq1
    ineq12d
    eqeq12d
    vx
    @7
    @1
    @11
    vy
    vex
    vx
    @9
    @10
    vx
    @7
    cB
    nfcsb1v
    vx
    @7
    cC
    nfcsb1v
    nfin
    vx
    vy
    weq
    cB
    @9
    cC
    @10
    vx
    @7
    cB
    csbeq1a
    vx
    @7
    cC
    csbeq1a
    ineq12d
    csbief
    vtoclg
    @0
    wn
    #
    @2
    c0
    @5
    vx
    cA
    @1
    csbprc
    @13
    @5
    c0
    c0
    cin
    c0
    @13
    @3
    c0
    @4
    c0
    vx
    cA
    cB
    csbprc
    vx
    cA
    cC
    csbprc
    ineq12d
    c0
    in0
    syl6req
    eqtrd
    pm2.61i
end
