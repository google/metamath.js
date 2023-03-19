include "cvv.mm"
include "wcel.mm"
include "co.mm"
include "csb.mm"
include "wceq.mm"
include "cv.mm"
include "csbeq1.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "vex.mm"
include "nfcsb1v.mm"
include "nfov.mm"
include "weq.mm"
include "csbeq1a.mm"
include "csbief.mm"
include "vtoclg.mm"
include "wn.mm"
include "c0.mm"
include "csbprc.mm"
include "cop.mm"
include "cfv.mm"
include "df-ov.mm"
include "fveq1d.mm"
include "0fv.mm"
include "syl6eq.mm"
include "syl5req.mm"
include "eqtrd.mm"
include "pm2.61i.mm"

theorem csbov123
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vy: setvar y


  assert |- [_ A / x ]_ ( B F C ) = ( [_ A / x ]_ B [_ A / x ]_ F [_ A / x ]_ C )

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    cB
    cC
    cF
    co
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
    vx
    cA
    cF
    csb
    #
    co
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
    @8
    cB
    csb
    #
    vx
    @8
    cC
    csb
    #
    vx
    @8
    cF
    csb
    #
    co
    #
    wceq
    @7
    vy
    cA
    cvv
    @8
    cA
    wceq
    #
    @9
    @2
    @13
    @6
    vx
    @8
    cA
    @1
    csbeq1
    @14
    @10
    @3
    @11
    @4
    @12
    @5
    vx
    @8
    cA
    cF
    csbeq1
    vx
    @8
    cA
    cB
    csbeq1
    vx
    @8
    cA
    cC
    csbeq1
    oveq123d
    eqeq12d
    vx
    @8
    @1
    @13
    vy
    vex
    vx
    @10
    @11
    @12
    vx
    @8
    cB
    nfcsb1v
    vx
    @8
    cF
    nfcsb1v
    vx
    @8
    cC
    nfcsb1v
    nfov
    vx
    vy
    weq
    cB
    @10
    cC
    @11
    cF
    @12
    vx
    @8
    cF
    csbeq1a
    vx
    @8
    cB
    csbeq1a
    vx
    @8
    cC
    csbeq1a
    oveq123d
    csbief
    vtoclg
    @0
    wn
    #
    @2
    c0
    @6
    vx
    cA
    @1
    csbprc
    @15
    @6
    @3
    @4
    cop
    #
    @5
    cfv
    #
    c0
    @3
    @4
    @5
    df-ov
    @15
    @17
    @16
    c0
    cfv
    c0
    @15
    @16
    @5
    c0
    vx
    cA
    cF
    csbprc
    fveq1d
    @16
    0fv
    syl6eq
    syl5req
    eqtrd
    pm2.61i
end
