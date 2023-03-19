include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ctopon.mm"
include "ctop.mm"
include "mopntopon.mm"
include "topontop.mm"
include "syl.mm"

theorem mopntop
  let cD: class D
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vd: setvar d
  assume mopnval.1: |- J = ( MetOpen ` D )


  assert |- ( D e. ( *Met ` X ) -> J e. Top )

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
    cJ
    ctop
    wcel
    cD
    cJ
    cX
    mopnval.1
    mopntopon
    cX
    cJ
    topontop
    syl
end
