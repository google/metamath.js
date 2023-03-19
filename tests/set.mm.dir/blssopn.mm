include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cbl.mm"
include "crn.mm"
include "ctg.mm"
include "ctb.mm"
include "wss.mm"
include "blbas.mm"
include "bastg.mm"
include "syl.mm"
include "mopnval.mm"
include "sseqtr4d.mm"

theorem blssopn
  let cD: class D
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cR: class R
  let cS: class S
  let cN: class N
  let cP: class P
  let cT: class T
  assume mopni.1: |- J = ( MetOpen ` D )


  assert |- ( D e. ( *Met ` X ) -> ran ( ball ` D ) C_ J )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cD
    cbl
    cfv
    crn
    #
    @1
    ctg
    cfv
    #
    cJ
    @0
    @1
    ctb
    wcel
    @1
    @2
    wss
    cD
    cX
    blbas
    @1
    ctb
    bastg
    syl
    cD
    cJ
    cX
    mopni.1
    mopnval
    sseqtr4d
end
