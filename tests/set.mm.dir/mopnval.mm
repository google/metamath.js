include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "crn.mm"
include "cuni.mm"
include "cbl.mm"
include "ctg.mm"
include "wceq.mm"
include "fvssunirn.mm"
include "sseli.mm"
include "cmopn.mm"
include "cv.mm"
include "fveq2.mm"
include "rneqd.mm"
include "fveq2d.mm"
include "df-mopn.mm"
include "fvex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem mopnval
  let cD: class D
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vd: setvar d
  assume mopnval.1: |- J = ( MetOpen ` D )


  assert |- ( D e. ( *Met ` X ) -> J = ( topGen ` ran ( ball ` D ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    #
    wcel
    cD
    cxmt
    crn
    cuni
    #
    wcel
    #
    cJ
    cD
    cbl
    cfv
    #
    crn
    #
    ctg
    cfv
    #
    wceq
    @0
    @1
    cD
    cxmt
    cX
    fvssunirn
    sseli
    @2
    cJ
    cD
    cmopn
    cfv
    @5
    mopnval.1
    vd
    cD
    vd
    cv
    #
    cbl
    cfv
    #
    crn
    #
    ctg
    cfv
    @5
    @1
    cmopn
    @6
    cD
    wceq
    #
    @8
    @4
    ctg
    @9
    @7
    @3
    @6
    cD
    cbl
    fveq2
    rneqd
    fveq2d
    vd
    df-mopn
    @4
    ctg
    fvex
    fvmpt
    syl5eq
    syl
end
