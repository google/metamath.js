include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "wss.mm"
include "cuni.mm"
include "mopntop.mm"
include "uniopn.mm"
include "sylan.mm"

theorem unimopn
  let cA: class A
  let cD: class D
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cR: class R
  let cS: class S
  let cN: class N
  let cP: class P
  let cT: class T
  assume mopni.1: |- J = ( MetOpen ` D )


  assert |- ( ( D e. ( *Met ` X ) /\ A C_ J ) -> U. A e. J )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cJ
    ctop
    wcel
    cA
    cJ
    wss
    cA
    cuni
    cJ
    wcel
    cD
    cJ
    cX
    mopni.1
    mopntop
    cA
    cJ
    uniopn
    sylan
end
