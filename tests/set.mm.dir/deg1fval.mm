include "cdg1.mm"
include "cfv.mm"
include "c1o.mm"
include "cmdg.mm"
include "co.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "oveq2.mm"
include "df-deg1.mm"
include "ovex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "reldmmdeg.mm"
include "ovprc2.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem deg1fval
  let cD: class D
  let cR: class R
  let vr: setvar r
  assume deg1fval.d: |- D = ( deg1 ` R )


  assert |- D = ( 1o mDeg R )

  proof
    cD
    cR
    cdg1
    cfv
    #
    c1o
    cR
    cmdg
    co
    #
    deg1fval.d
    cR
    cvv
    wcel
    #
    @0
    @1
    wceq
    vr
    cR
    c1o
    vr
    cv
    #
    cmdg
    co
    @1
    cvv
    cdg1
    @3
    cR
    c1o
    cmdg
    oveq2
    vr
    df-deg1
    c1o
    cR
    cmdg
    ovex
    fvmpt
    @2
    wn
    @0
    c0
    @1
    cR
    cdg1
    fvprc
    c1o
    cR
    cmdg
    reldmmdeg
    ovprc2
    eqtr4d
    pm2.61i
    eqtri
end
