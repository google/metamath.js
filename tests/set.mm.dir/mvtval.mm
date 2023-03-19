include "cmvt.mm"
include "cfv.mm"
include "cmty.mm"
include "crn.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "fveq2.mm"
include "rneqd.mm"
include "df-mvt.mm"
include "fvex.mm"
include "rnex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "rn0.mm"
include "eqcomi.mm"
include "fvprc.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "rneqi.mm"
include "3eqtr4i.mm"

theorem mvtval
  let cT: class T
  let cV: class V
  let cY: class Y
  let vt: setvar t
  assume mvtval.f: |- V = ( mVT ` T )
  assume mvtval.y: |- Y = ( mType ` T )


  assert |- V = ran Y

  proof
    cT
    cmvt
    cfv
    #
    cT
    cmty
    cfv
    #
    crn
    #
    cV
    cY
    crn
    cT
    cvv
    wcel
    #
    @0
    @2
    wceq
    vt
    cT
    vt
    cv
    #
    cmty
    cfv
    #
    crn
    @2
    cvv
    cmvt
    @4
    cT
    wceq
    @5
    @1
    @4
    cT
    cmty
    fveq2
    rneqd
    vt
    df-mvt
    @1
    cT
    cmty
    fvex
    rnex
    fvmpt
    @3
    wn
    #
    c0
    c0
    crn
    #
    @0
    @2
    @7
    c0
    rn0
    eqcomi
    cT
    cmvt
    fvprc
    @6
    @1
    c0
    cT
    cmty
    fvprc
    rneqd
    3eqtr4a
    pm2.61i
    mvtval.f
    cY
    @1
    mvtval.y
    rneqi
    3eqtr4i
end
