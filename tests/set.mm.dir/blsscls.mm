include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cbl.mm"
include "co.mm"
include "ccl.mm"
include "cv.mm"
include "cle.mm"
include "crab.mm"
include "wss.mm"
include "eqid.mm"
include "blcls.mm"
include "3expa.mm"
include "3ad2antr1.mm"
include "blsscls2.mm"
include "sstrd.mm"

theorem blsscls
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let cJ: class J
  let cX: class X
  let vx: setvar x
  assume blsscls.2: |- J = ( MetOpen ` D )


  assert |- ( ( ( D e. ( *Met ` X ) /\ P e. X ) /\ ( R e. RR* /\ S e. RR* /\ R < S ) ) -> ( ( cls ` J ) ` ( P ( ball ` D ) R ) ) C_ ( P ( ball ` D ) S ) )

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
    wa
    #
    cR
    cxr
    wcel
    #
    cS
    cxr
    wcel
    #
    cR
    cS
    clt
    wbr
    #
    w3a
    wa
    cP
    cR
    cD
    cbl
    cfv
    #
    co
    cJ
    ccl
    cfv
    cfv
    #
    cP
    vx
    cv
    cD
    co
    cR
    cle
    wbr
    vx
    cX
    crab
    #
    cP
    cS
    @6
    co
    @2
    @4
    @3
    @7
    @8
    wss
    #
    @5
    @0
    @1
    @3
    @9
    vx
    cD
    cP
    cR
    @8
    cJ
    cX
    blsscls.2
    @8
    eqid
    #
    blcls
    3expa
    3ad2antr1
    vx
    cD
    cP
    cR
    @8
    cS
    cJ
    cX
    blsscls.2
    @10
    blsscls2
    sstrd
end
