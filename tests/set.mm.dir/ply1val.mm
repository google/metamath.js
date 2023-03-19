include "cpl1.mm"
include "cfv.mm"
include "c1o.mm"
include "cmpl.mm"
include "co.mm"
include "cbs.mm"
include "cress.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cps1.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "df-ply1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "ress0.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem ply1val
  let cP: class P
  let cR: class R
  let cS: class S
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  assume ply1val.1: |- P = ( Poly1 ` R )
  assume ply1val.2: |- S = ( PwSer1 ` R )


  assert |- P = ( S |`s ( Base ` ( 1o mPoly R ) ) )

  proof
    cP
    cR
    cpl1
    cfv
    #
    cS
    c1o
    cR
    cmpl
    co
    #
    cbs
    cfv
    #
    cress
    co
    #
    ply1val.1
    cR
    cvv
    wcel
    #
    @0
    @3
    wceq
    vr
    cR
    vr
    cv
    #
    cps1
    cfv
    #
    c1o
    @5
    cmpl
    co
    #
    cbs
    cfv
    #
    cress
    co
    @3
    cvv
    cpl1
    @5
    cR
    wceq
    #
    @6
    cS
    @8
    @2
    cress
    @9
    @6
    cR
    cps1
    cfv
    #
    cS
    @5
    cR
    cps1
    fveq2
    ply1val.2
    syl6eqr
    @9
    @7
    @1
    cbs
    @5
    cR
    c1o
    cmpl
    oveq2
    fveq2d
    oveq12d
    vr
    df-ply1
    cS
    @2
    cress
    ovex
    fvmpt
    @4
    wn
    #
    @0
    c0
    @2
    cress
    co
    #
    @3
    @11
    @0
    c0
    @12
    cR
    cpl1
    fvprc
    @2
    ress0
    syl6eqr
    @11
    cS
    c0
    @2
    cress
    @11
    cS
    @10
    c0
    ply1val.2
    cR
    cps1
    fvprc
    syl5eq
    oveq1d
    eqtr4d
    pm2.61i
    eqtri
end
