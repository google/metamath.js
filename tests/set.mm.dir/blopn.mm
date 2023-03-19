include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "w3a.mm"
include "cbl.mm"
include "crn.mm"
include "co.mm"
include "wss.mm"
include "blssopn.mm"
include "3ad2ant1.mm"
include "blelrn.mm"
include "sseldd.mm"

theorem blopn
  let cD: class D
  let cP: class P
  let cR: class R
  let cJ: class J
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let cS: class S
  let cN: class N
  let cT: class T
  assume mopni.1: |- J = ( MetOpen ` D )


  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ R e. RR* ) -> ( P ( ball ` D ) R ) e. J )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cR
    cxr
    wcel
    #
    w3a
    cD
    cbl
    cfv
    #
    crn
    #
    cJ
    cP
    cR
    @3
    co
    @0
    @1
    @4
    cJ
    wss
    @2
    cD
    cJ
    cX
    mopni.1
    blssopn
    3ad2ant1
    cD
    cP
    cR
    cX
    blelrn
    sseldd
end
