include "cps.mm"
include "wcel.mm"
include "cordt.mm"
include "cfv.mm"
include "ctop.mm"
include "cv.mm"
include "csn.mm"
include "ccld.mm"
include "cuni.mm"
include "wral.mm"
include "ct1.mm"
include "ordttop.mm"
include "cdm.mm"
include "wa.mm"
include "wbr.mm"
include "crab.mm"
include "cin.mm"
include "wss.mm"
include "wceq.mm"
include "snssi.mm"
include "adantl.mm"
include "sseqin2.mm"
include "sylib.mm"
include "velsn.mm"
include "eqid.mm"
include "psref.mm"
include "adantr.mm"
include "jca.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "wi.mm"
include "w3a.mm"
include "psasym.mm"
include "eqcomd.mm"
include "3expib.mm"
include "ad2antrr.mm"
include "impbid.mm"
include "syl5bb.mm"
include "rabbi2dva.mm"
include "eqtr3d.mm"
include "ordtcld3.mm"
include "3anidm23.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "ctopon.mm"
include "ordttopon.mm"
include "toponuni.mm"
include "syl.mm"
include "raleqdv.mm"
include "mpbid.mm"
include "ist1.mm"
include "sylanbrc.mm"

theorem ordtt1
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( R e. PosetRel -> ( ordTop ` R ) e. Fre )

  proof
    cR
    cps
    wcel
    #
    cR
    cordt
    cfv
    #
    ctop
    wcel
    vx
    cv
    #
    csn
    #
    @1
    ccld
    cfv
    #
    wcel
    #
    vx
    @1
    cuni
    #
    wral
    #
    @1
    ct1
    wcel
    cR
    cps
    ordttop
    @0
    @5
    vx
    cR
    cdm
    #
    wral
    @7
    @0
    @5
    vx
    @8
    @0
    @2
    @8
    wcel
    #
    wa
    #
    @3
    @2
    vy
    cv
    #
    cR
    wbr
    #
    @11
    @2
    cR
    wbr
    #
    wa
    #
    vy
    @8
    crab
    #
    @4
    @10
    @8
    @3
    cin
    #
    @3
    @15
    @10
    @3
    @8
    wss
    #
    @16
    @3
    wceq
    @9
    @17
    @0
    @2
    @8
    snssi
    adantl
    @3
    @8
    sseqin2
    sylib
    @10
    @14
    vy
    @8
    @3
    @11
    @3
    wcel
    @11
    @2
    wceq
    #
    @10
    @11
    @8
    wcel
    #
    wa
    #
    @14
    vy
    @2
    velsn
    @20
    @18
    @14
    @20
    @14
    @18
    @2
    @2
    cR
    wbr
    #
    @21
    wa
    @20
    @21
    @21
    @10
    @21
    @19
    @2
    cR
    @8
    @8
    eqid
    #
    psref
    adantr
    #
    @23
    jca
    @18
    @12
    @21
    @13
    @21
    @11
    @2
    @2
    cR
    breq2
    @11
    @2
    @2
    cR
    breq1
    anbi12d
    syl5ibrcom
    @0
    @14
    @18
    wi
    @9
    @19
    @0
    @12
    @13
    @18
    @0
    @12
    @13
    w3a
    @2
    @11
    @2
    @11
    cR
    psasym
    eqcomd
    3expib
    ad2antrr
    impbid
    syl5bb
    rabbi2dva
    eqtr3d
    @0
    @9
    @15
    @4
    wcel
    vy
    @2
    @2
    cR
    cps
    @8
    @22
    ordtcld3
    3anidm23
    eqeltrd
    ralrimiva
    @0
    @5
    vx
    @8
    @6
    @0
    @1
    @8
    ctopon
    cfv
    wcel
    @8
    @6
    wceq
    cR
    cps
    @8
    @22
    ordttopon
    @8
    @1
    toponuni
    syl
    raleqdv
    mpbid
    @1
    @6
    vx
    @6
    eqid
    ist1
    sylanbrc
end
