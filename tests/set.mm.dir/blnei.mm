include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "ctop.mm"
include "cbl.mm"
include "co.mm"
include "csn.mm"
include "cnei.mm"
include "mopntop.mm"
include "3ad2ant1.mm"
include "cxr.mm"
include "rpxr.mm"
include "blopn.mm"
include "syl3an3.mm"
include "blcntr.mm"
include "opnneip.mm"
include "syl3anc.mm"

theorem blnei
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


  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ R e. RR+ ) -> ( P ( ball ` D ) R ) e. ( ( nei ` J ) ` { P } ) )

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
    crp
    wcel
    #
    w3a
    cJ
    ctop
    wcel
    #
    cP
    cR
    cD
    cbl
    cfv
    co
    #
    cJ
    wcel
    #
    cP
    @4
    wcel
    @4
    cP
    csn
    cJ
    cnei
    cfv
    cfv
    wcel
    @0
    @1
    @3
    @2
    cD
    cJ
    cX
    mopni.1
    mopntop
    3ad2ant1
    @2
    @0
    @1
    cR
    cxr
    wcel
    @5
    cR
    rpxr
    cD
    cP
    cR
    cJ
    cX
    mopni.1
    blopn
    syl3an3
    cD
    cP
    cR
    cX
    blcntr
    cP
    cJ
    @4
    opnneip
    syl3anc
end
