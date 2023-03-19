include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ctopon.mm"
include "wss.mm"
include "mopntopon.mm"
include "toponss.mm"
include "sylan.mm"

theorem mopnss
  let cA: class A
  let cD: class D
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  assume mopnval.1: |- J = ( MetOpen ` D )


  assert |- ( ( D e. ( *Met ` X ) /\ A e. J ) -> A C_ X )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cJ
    cX
    ctopon
    cfv
    wcel
    cA
    cJ
    wcel
    cA
    cX
    wss
    cD
    cJ
    cX
    mopnval.1
    mopntopon
    cA
    cJ
    cX
    toponss
    sylan
end
