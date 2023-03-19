include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cbl.mm"
include "crn.mm"
include "blssopn.mm"
include "sselda.mm"

theorem rnblopn
  let cB: class B
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


  assert |- ( ( D e. ( *Met ` X ) /\ B e. ran ( ball ` D ) ) -> B e. J )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cD
    cbl
    cfv
    crn
    cJ
    cB
    cD
    cJ
    cX
    mopni.1
    blssopn
    sselda
end
