include "cv.mm"
include "wcel.mm"
include "cmsr.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "mthmi.mm"
include "mpan2.mm"
include "ssriv.mm"

theorem mppsthm
  let cT: class T
  let cU: class U
  let cJ: class J
  let vx: setvar x
  assume mppsthm.j: |- J = ( mPPSt ` T )
  assume mppsthm.u: |- U = ( mThm ` T )


  assert |- J C_ U

  proof
    vx
    cJ
    cU
    vx
    cv
    #
    cJ
    wcel
    @0
    cT
    cmsr
    cfv
    #
    cfv
    #
    @2
    wceq
    @0
    cU
    wcel
    @2
    eqid
    @1
    cT
    cU
    cJ
    @0
    @0
    @1
    eqid
    mppsthm.j
    mppsthm.u
    mthmi
    mpan2
    ssriv
end
