include "cmsta.mm"
include "cfv.mm"
include "crn.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "cmsr.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "rneqd.mm"
include "df-msta.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rnex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "rn0.mm"
include "eqcomi.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem mstaval
  let cR: class R
  let cS: class S
  let cT: class T
  let vs: setvar s
  let vt: setvar t
  let cX: class X
  assume mstaval.r: |- R = ( mStRed ` T )
  assume mstaval.s: |- S = ( mStat ` T )


  assert |- S = ran R

  proof
    cS
    cT
    cmsta
    cfv
    #
    cR
    crn
    #
    mstaval.s
    cT
    cvv
    wcel
    #
    @0
    @1
    wceq
    vt
    cT
    vt
    cv
    #
    cmsr
    cfv
    #
    crn
    @1
    cvv
    cmsta
    @3
    cT
    wceq
    #
    @4
    cR
    @5
    @4
    cT
    cmsr
    cfv
    #
    cR
    @3
    cT
    cmsr
    fveq2
    mstaval.r
    syl6eqr
    rneqd
    vt
    df-msta
    cR
    cR
    @6
    cvv
    mstaval.r
    cT
    cmsr
    fvex
    eqeltri
    rnex
    fvmpt
    @2
    wn
    #
    c0
    c0
    crn
    #
    @0
    @1
    @8
    c0
    rn0
    eqcomi
    cT
    cmsta
    fvprc
    @7
    cR
    c0
    @7
    cR
    @6
    c0
    mstaval.r
    cT
    cmsr
    fvprc
    syl5eq
    rneqd
    3eqtr4a
    pm2.61i
    eqtri
end
