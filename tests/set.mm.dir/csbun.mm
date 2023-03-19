include "cvv.mm"
include "wcel.mm"
include "cun.mm"
include "csb.mm"
include "wceq.mm"
include "cv.mm"
include "csbeq1.mm"
include "uneq12d.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfcsb1v.mm"
include "nfun.mm"
include "weq.mm"
include "csbeq1a.mm"
include "csbief.mm"
include "vtoclg.mm"
include "wn.mm"
include "c0.mm"
include "un0.mm"
include "a1i.mm"
include "csbprc.mm"
include "3eqtr4rd.mm"
include "pm2.61i.mm"

theorem csbun
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vy: setvar y


  assert |- [_ A / x ]_ ( B u. C ) = ( [_ A / x ]_ B u. [_ A / x ]_ C )

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    cB
    cC
    cun
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
    cun
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
    cun
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
    uneq12d
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
    nfun
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
    uneq12d
    csbief
    vtoclg
    @0
    wn
    #
    c0
    c0
    cun
    #
    c0
    @5
    @2
    @14
    c0
    wceq
    @13
    c0
    un0
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
    uneq12d
    vx
    cA
    @1
    csbprc
    3eqtr4rd
    pm2.61i
end
