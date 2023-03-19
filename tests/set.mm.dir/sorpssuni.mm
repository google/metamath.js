include "crpss.mm"
include "wor.mm"
include "cv.mm"
include "wpss.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "cuni.mm"
include "wcel.mm"
include "w3a.mm"
include "wss.mm"
include "wa.mm"
include "wo.mm"
include "wi.mm"
include "sorpssi.mm"
include "anassrs.mm"
include "weq.mm"
include "sspss.mm"
include "orel1.mm"
include "eqimss2.mm"
include "syl6com.mm"
include "sylbi.mm"
include "ax-1.mm"
include "jaoi.mm"
include "syl.mm"
include "ralimdva.mm"
include "3impia.mm"
include "unissb.mm"
include "sylibr.mm"
include "elssuni.mm"
include "3ad2ant2.mm"
include "eqssd.mm"
include "simp2.mm"
include "eqeltrd.mm"
include "rexlimdv3a.mm"
include "ssnpss.mm"
include "rgen.mm"
include "wceq.mm"
include "psseq1.mm"
include "notbid.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "mpan2.mm"
include "impbid1.mm"

theorem sorpssuni
  let vv: setvar v
  let vu: setvar u
  let cY: class Y

  disjoint Y u
  disjoint Y v
  disjoint u v
  assert |- ( [C.] Or Y -> ( E. u e. Y A. v e. Y -. u C. v <-> U. Y e. Y ) )

  proof
    cY
    crpss
    wor
    #
    vu
    cv
    #
    vv
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
    cuni
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
    @1
    cY
    wcel
    #
    @5
    w3a
    #
    @7
    @1
    cY
    @10
    @7
    @1
    @10
    @2
    @1
    wss
    #
    vv
    cY
    wral
    #
    @7
    @1
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
    @2
    cY
    wcel
    #
    wa
    @1
    @2
    wss
    #
    @11
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
    @1
    @2
    sorpssi
    anassrs
    @15
    @17
    @11
    @15
    @3
    vu
    vv
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
    @11
    @4
    ax-1
    jaoi
    syl
    ralimdva
    3impia
    vv
    cY
    @1
    unissb
    sylibr
    @9
    @0
    @1
    @7
    wss
    @5
    @1
    cY
    elssuni
    3ad2ant2
    eqssd
    @0
    @9
    @5
    simp2
    eqeltrd
    rexlimdv3a
    @8
    @7
    @2
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
    @2
    @7
    wss
    @21
    @2
    cY
    elssuni
    @2
    @7
    ssnpss
    syl
    rgen
    @5
    @22
    vu
    @7
    cY
    @1
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
    @1
    @7
    @2
    psseq1
    notbid
    ralbidv
    rspcev
    mpan2
    impbid1
end
