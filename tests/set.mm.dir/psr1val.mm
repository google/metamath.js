include "cps1.mm"
include "cfv.mm"
include "c0.mm"
include "c1o.mm"
include "copws.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "oveq2.mm"
include "fveq1d.mm"
include "df-psr1.mm"
include "fvex.mm"
include "fvmpt.mm"
include "wn.mm"
include "0fv.mm"
include "eqcomi.mm"
include "fvprc.mm"
include "reldmopsr.mm"
include "ovprc2.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem psr1val
  let cR: class R
  let cS: class S
  let vr: setvar r
  assume psr1val.1: |- S = ( PwSer1 ` R )


  assert |- S = ( ( 1o ordPwSer R ) ` (/) )

  proof
    cS
    cR
    cps1
    cfv
    #
    c0
    c1o
    cR
    copws
    co
    #
    cfv
    #
    psr1val.1
    cR
    cvv
    wcel
    #
    @0
    @2
    wceq
    vr
    cR
    c0
    c1o
    vr
    cv
    #
    copws
    co
    #
    cfv
    @2
    cvv
    cps1
    @4
    cR
    wceq
    c0
    @5
    @1
    @4
    cR
    c1o
    copws
    oveq2
    fveq1d
    vr
    df-psr1
    c0
    @1
    fvex
    fvmpt
    @3
    wn
    #
    c0
    c0
    c0
    cfv
    #
    @0
    @2
    @7
    c0
    c0
    0fv
    eqcomi
    cR
    cps1
    fvprc
    @6
    c0
    @1
    c0
    c1o
    cR
    copws
    reldmopsr
    ovprc2
    fveq1d
    3eqtr4a
    pm2.61i
    eqtri
end
