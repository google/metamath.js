include "cvv.mm"
include "wcel.mm"
include "cima.mm"
include "csb.mm"
include "wceq.mm"
include "cv.mm"
include "csbeq1.mm"
include "imaeq12d.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfcsb1v.mm"
include "nfima.mm"
include "weq.mm"
include "csbeq1a.mm"
include "csbief.mm"
include "vtoclg.mm"
include "wn.mm"
include "c0.mm"
include "csbprc.mm"
include "imaeq2d.mm"
include "ima0.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "pm2.61i.mm"

theorem csbima12
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y


  assert |- [_ A / x ]_ ( F " B ) = ( [_ A / x ]_ F " [_ A / x ]_ B )

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    cF
    cB
    cima
    #
    csb
    #
    vx
    cA
    cF
    csb
    #
    vx
    cA
    cB
    csb
    #
    cima
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
    cF
    csb
    #
    vx
    @7
    cB
    csb
    #
    cima
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
    cF
    csbeq1
    vx
    @7
    cA
    cB
    csbeq1
    imaeq12d
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
    cF
    nfcsb1v
    vx
    @7
    cB
    nfcsb1v
    nfima
    vx
    vy
    weq
    cF
    @9
    cB
    @10
    vx
    @7
    cF
    csbeq1a
    vx
    @7
    cB
    csbeq1a
    imaeq12d
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
    @3
    c0
    cima
    c0
    @13
    @4
    c0
    @3
    vx
    cA
    cB
    csbprc
    imaeq2d
    @3
    ima0
    syl6req
    eqtrd
    pm2.61i
end
