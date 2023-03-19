include "cvv.mm"
include "wcel.mm"
include "cdif.mm"
include "csb.mm"
include "wceq.mm"
include "cv.mm"
include "csbeq1.mm"
include "difeq12d.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfcsb1v.mm"
include "nfdif.mm"
include "csbeq1a.mm"
include "csbief.mm"
include "vtoclg.mm"
include "wn.mm"
include "c0.mm"
include "dif0.mm"
include "a1i.mm"
include "csbprc.mm"
include "3eqtr4rd.mm"
include "pm2.61i.mm"

theorem csbdif
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- [_ A / x ]_ ( B \ C ) = ( [_ A / x ]_ B \ [_ A / x ]_ C )

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    cB
    cC
    cdif
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
    cdif
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
    cdif
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
    difeq12d
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
    nfdif
    vx
    cv
    @7
    wceq
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
    difeq12d
    csbief
    vtoclg
    @0
    wn
    #
    c0
    c0
    cdif
    #
    c0
    @5
    @2
    @14
    c0
    wceq
    @13
    c0
    dif0
    a1i
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
    difeq12d
    vx
    cA
    @1
    csbprc
    3eqtr4rd
    pm2.61i
end
