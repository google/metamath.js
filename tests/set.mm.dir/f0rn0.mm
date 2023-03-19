include "wf.mm"
include "cv.mm"
include "crn.mm"
include "wcel.mm"
include "wrex.mm"
include "wn.mm"
include "c0.mm"
include "wceq.mm"
include "cdm.mm"
include "wi.mm"
include "fdm.mm"
include "wa.mm"
include "wss.mm"
include "frn.mm"
include "wral.mm"
include "ralnex.mm"
include "cin.mm"
include "disj.mm"
include "df-ss.mm"
include "incom.mm"
include "eqeq1i.mm"
include "eqtr2.mm"
include "ex.mm"
include "sylbi.mm"
include "syl5bir.mm"
include "syl.mm"
include "imp.mm"
include "adantl.mm"
include "dm0rn0.mm"
include "sylibr.mm"
include "wb.mm"
include "eqeq1.mm"
include "eqcoms.mm"
include "adantr.mm"
include "mpbird.mm"
include "exp32.mm"
include "mpcom.mm"

theorem f0rn0
  let vy: setvar y
  let cE: class E
  let cX: class X
  let cY: class Y

  disjoint E y
  disjoint Y y
  assert |- ( ( E : X --> Y /\ -. E. y e. Y y e. ran E ) -> X = (/) )

  proof
    cX
    cY
    cE
    wf
    #
    vy
    cv
    cE
    crn
    #
    wcel
    #
    vy
    cY
    wrex
    wn
    #
    cX
    c0
    wceq
    #
    cE
    cdm
    #
    cX
    wceq
    #
    @0
    @3
    @4
    wi
    cX
    cY
    cE
    fdm
    @6
    @0
    @3
    @4
    @6
    @0
    @3
    wa
    #
    wa
    #
    @4
    @5
    c0
    wceq
    #
    @8
    @1
    c0
    wceq
    #
    @9
    @7
    @10
    @6
    @0
    @3
    @10
    @0
    @1
    cY
    wss
    #
    @3
    @10
    wi
    cX
    cY
    cE
    frn
    @3
    @2
    wn
    vy
    cY
    wral
    #
    @11
    @10
    @2
    vy
    cY
    ralnex
    @12
    cY
    @1
    cin
    #
    c0
    wceq
    #
    @11
    @10
    vy
    cY
    @1
    disj
    @11
    @1
    cY
    cin
    #
    @1
    wceq
    #
    @14
    @10
    wi
    #
    @1
    cY
    df-ss
    @16
    @13
    @1
    wceq
    #
    @17
    @15
    @13
    @1
    @1
    cY
    incom
    eqeq1i
    @18
    @14
    @10
    @13
    @1
    c0
    eqtr2
    ex
    sylbi
    sylbi
    syl5bir
    syl5bir
    syl
    imp
    adantl
    cE
    dm0rn0
    sylibr
    @6
    @4
    @9
    wb
    #
    @7
    @19
    cX
    @5
    cX
    @5
    c0
    eqeq1
    eqcoms
    adantr
    mpbird
    exp32
    mpcom
    imp
end
