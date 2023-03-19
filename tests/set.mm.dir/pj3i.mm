include "cpjh.mm"
include "cfv.mm"
include "ccom.mm"
include "wceq.mm"
include "crn.mm"
include "wss.mm"
include "cin.mm"
include "coass.mm"
include "eqeq1.mm"
include "mpbiri.mm"
include "rneqd.mm"
include "rncoss.mm"
include "pjrni.mm"
include "sseqtri.mm"
include "syl6eqss.mm"
include "pj3si.mm"
include "sylan2.mm"

theorem pj3i
  let cF: class F
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  assume pjadj2co.1: |- F e. CH
  assume pjadj2co.2: |- G e. CH
  assume pjadj2co.3: |- H e. CH


  assert |- ( ( ( ( ( projh ` F ) o. ( projh ` G ) ) o. ( projh ` H ) ) = ( ( ( projh ` H ) o. ( projh ` G ) ) o. ( projh ` F ) ) /\ ( ( ( projh ` F ) o. ( projh ` G ) ) o. ( projh ` H ) ) = ( ( ( projh ` G ) o. ( projh ` F ) ) o. ( projh ` H ) ) ) -> ( ( ( projh ` F ) o. ( projh ` G ) ) o. ( projh ` H ) ) = ( projh ` ( ( F i^i G ) i^i H ) ) )

  proof
    cF
    cpjh
    cfv
    #
    cG
    cpjh
    cfv
    #
    ccom
    cH
    cpjh
    cfv
    #
    ccom
    #
    @1
    @0
    ccom
    @2
    ccom
    #
    wceq
    #
    @3
    @2
    @1
    ccom
    @0
    ccom
    wceq
    @3
    crn
    #
    cG
    wss
    @3
    cF
    cG
    cin
    cH
    cin
    cpjh
    cfv
    wceq
    @5
    @6
    @1
    @0
    @2
    ccom
    #
    ccom
    #
    crn
    #
    cG
    @5
    @3
    @8
    @5
    @3
    @8
    wceq
    @4
    @8
    wceq
    @1
    @0
    @2
    coass
    @3
    @4
    @8
    eqeq1
    mpbiri
    rneqd
    @9
    @1
    crn
    cG
    @1
    @7
    rncoss
    cG
    pjadj2co.2
    pjrni
    sseqtri
    syl6eqss
    cF
    cG
    cH
    pjadj2co.1
    pjadj2co.2
    pjadj2co.3
    pj3si
    sylan2
end
