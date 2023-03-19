include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cuni.mm"
include "cpw.mm"
include "pwuni.mm"
include "mopnuni.mm"
include "pweqd.mm"
include "syl5sseqr.mm"

theorem mopnfss
  let cD: class D
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vd: setvar d
  assume mopnval.1: |- J = ( MetOpen ` D )


  assert |- ( D e. ( *Met ` X ) -> J C_ ~P X )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cJ
    cuni
    #
    cpw
    cJ
    cX
    cpw
    cJ
    pwuni
    @0
    cX
    @1
    cD
    cJ
    cX
    mopnval.1
    mopnuni
    pweqd
    syl5sseqr
end
