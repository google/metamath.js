include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "c0.mm"
include "mopntop.mm"
include "0opn.mm"
include "syl.mm"

theorem mopn0
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


  assert |- ( D e. ( *Met ` X ) -> (/) e. J )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cJ
    ctop
    wcel
    c0
    cJ
    wcel
    cD
    cJ
    cX
    mopni.1
    mopntop
    cJ
    0opn
    syl
end
