include "cvv.mm"
include "wcel.mm"
include "cfv.mm"
include "csb.mm"
include "wceq.mm"
include "cv.mm"
include "wbr.mm"
include "cio.mm"
include "wsbc.mm"
include "csbiota.mm"
include "sbcbr123.mm"
include "csbconstg.mm"
include "breq2d.mm"
include "syl5bb.mm"
include "iotabidv.mm"
include "syl5eq.mm"
include "df-fv.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"
include "wn.mm"
include "c0.mm"
include "csbprc.mm"
include "fveq1d.mm"
include "0fv.mm"
include "syl6req.mm"
include "eqtrd.mm"
include "pm2.61i.mm"

theorem csbfv12
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let vy: setvar y


  assert |- [_ A / x ]_ ( F ` B ) = ( [_ A / x ]_ F ` [_ A / x ]_ B )

  proof
    cA
    cvv
    wcel
    #
    vx
    cA
    cB
    cF
    cfv
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
    cF
    csb
    #
    cfv
    #
    wceq
    @0
    vx
    cA
    cB
    vy
    cv
    #
    cF
    wbr
    #
    vy
    cio
    #
    csb
    #
    @3
    @6
    @4
    wbr
    #
    vy
    cio
    #
    @2
    @5
    @0
    @9
    @7
    vx
    cA
    wsbc
    #
    vy
    cio
    @11
    @7
    vx
    vy
    cA
    csbiota
    @0
    @12
    @10
    vy
    @12
    @3
    vx
    cA
    @6
    csb
    #
    @4
    wbr
    @0
    @10
    vx
    cA
    cB
    @6
    cF
    sbcbr123
    @0
    @13
    @6
    @3
    @4
    vx
    cA
    @6
    cvv
    csbconstg
    breq2d
    syl5bb
    iotabidv
    syl5eq
    vx
    cA
    @1
    @8
    vy
    cB
    cF
    df-fv
    csbeq2i
    vy
    @3
    @4
    df-fv
    3eqtr4g
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
    @14
    @5
    @3
    c0
    cfv
    c0
    @14
    @3
    @4
    c0
    vx
    cA
    cF
    csbprc
    fveq1d
    @3
    0fv
    syl6req
    eqtrd
    pm2.61i
end
