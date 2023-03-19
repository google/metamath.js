include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "ctop.mm"
include "cin.mm"
include "mopntop.mm"
include "inopn.mm"
include "syl3an1.mm"

theorem mopnin
  let cA: class A
  let cB: class B
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


  assert |- ( ( D e. ( *Met ` X ) /\ A e. J /\ B e. J ) -> ( A i^i B ) e. J )

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
    wcel
    cB
    cJ
    wcel
    cA
    cB
    cin
    cJ
    wcel
    cD
    cJ
    cX
    mopni.1
    mopntop
    cA
    cB
    cJ
    inopn
    syl3an1
end
