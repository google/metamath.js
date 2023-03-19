include "crpss.mm"
include "wor.mm"
include "cv.mm"
include "wpss.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cint.mm"
include "wcel.mm"
include "w3a.mm"
include "wss.mm"
include "intss1.mm"
include "3ad2ant2.mm"
include "wa.mm"
include "wo.mm"
include "wi.mm"
include "sorpssi.mm"
include "anassrs.mm"
include "ax-1.mm"
include "weq.mm"
include "sspss.mm"
include "orel1.mm"
include "eqimss2.mm"
include "syl6com.mm"
include "sylbi.mm"
include "jaoi.mm"
include "syl.mm"
include "ralimdva.mm"
include "3impia.mm"
include "ssint.mm"
include "sylibr.mm"
include "eqssd.mm"
include "simp2.mm"
include "eqeltrd.mm"
include "rexlimdv3a.mm"
include "ssnpss.mm"
include "rgen.mm"
include "wceq.mm"
include "psseq2.mm"
include "notbid.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mpan2.mm"
include "impbid1.mm"

theorem sorpssint
  let vv: setvar v
  let vu: setvar u
  let cY: class Y

  disjoint Y u
  disjoint Y v
  disjoint u v
  assert |- ( [C.] Or Y -> ( E. u e. Y A. v e. Y -. v C. u <-> |^| Y e. Y ) )

  proof
    cY
    crpss
    wor
    #
    vv
    cv
    #
    vu
    cv
    #
    wpss
    #
    wn
    #
    vv
    cY
    wral
    #
    vu
    cY
    wrex
    #
    cY
    cint
    #
    cY
    wcel
    #
    @0
    @5
    @8
    vu
    cY
    @0
    @2
    cY
    wcel
    #
    @5
    w3a
    #
    @7
    @2
    cY
    @10
    @7
    @2
    @9
    @0
    @7
    @2
    wss
    @5
    @2
    cY
    intss1
    3ad2ant2
    @10
    @2
    @1
    wss
    #
    vv
    cY
    wral
    #
    @2
    @7
    wss
    @0
    @9
    @5
    @12
    @0
    @9
    wa
    #
    @4
    @11
    vv
    cY
    @13
    @1
    cY
    wcel
    #
    wa
    @11
    @1
    @2
    wss
    #
    wo
    #
    @4
    @11
    wi
    #
    @0
    @9
    @14
    @16
    cY
    @2
    @1
    sorpssi
    anassrs
    @11
    @17
    @15
    @11
    @4
    ax-1
    @15
    @3
    vv
    vu
    weq
    #
    wo
    #
    @17
    @1
    @2
    sspss
    @4
    @19
    @18
    @11
    @3
    @18
    orel1
    @2
    @1
    eqimss2
    syl6com
    sylbi
    jaoi
    syl
    ralimdva
    3impia
    vv
    @2
    cY
    ssint
    sylibr
    eqssd
    @0
    @9
    @5
    simp2
    eqeltrd
    rexlimdv3a
    @8
    @1
    @7
    wpss
    #
    wn
    #
    vv
    cY
    wral
    #
    @6
    @21
    vv
    cY
    @14
    @7
    @1
    wss
    @21
    @1
    cY
    intss1
    @7
    @1
    ssnpss
    syl
    rgen
    @5
    @22
    vu
    @7
    cY
    @2
    @7
    wceq
    #
    @4
    @21
    vv
    cY
    @23
    @3
    @20
    @2
    @7
    @1
    psseq2
    notbid
    ralbidv
    rspcev
    mpan2
    impbid1
end
