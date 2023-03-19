include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ctopon.mm"
include "cuni.mm"
include "wceq.mm"
include "mopntopon.mm"
include "toponuni.mm"
include "syl.mm"

theorem mopnuni
  let cD: class D
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vd: setvar d
  assume mopnval.1: |- J = ( MetOpen ` D )


  assert |- ( D e. ( *Met ` X ) -> X = U. J )

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
    cX
    cJ
    cuni
    wceq
    cD
    cJ
    cX
    mopnval.1
    mopntopon
    cX
    cJ
    toponuni
    syl
end
