include "crngo.mm"
include "wcel.mm"
include "cdm.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "w3a.mm"
include "cmndo.mm"
include "c1st.mm"
include "cfv.mm"
include "crn.mm"
include "eqid.mm"
include "rngosm.mm"
include "rngoass.mm"
include "ralrimivvva.mm"
include "cablo.mm"
include "rngoi.mm"
include "simprrd.mm"
include "wb.mm"
include "rngorn1.mm"
include "xpid11.mm"
include "biimpri.mm"
include "feq23.mm"
include "mpancom.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "rexeqbi1dv.mm"
include "3anbi123d.mm"
include "eqcoms.mm"
include "syl.mm"
include "mpbir3and.mm"
include "c2nd.mm"
include "cvv.mm"
include "fvex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "ismndo1.mm"
include "mp2b.mm"
include "sylibr.mm"

theorem rngomndo
  let cR: class R
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume unmnd.1: |- H = ( 2nd ` R )


  assert |- ( R e. RingOps -> H e. MndOp )

  proof
    cR
    crngo
    wcel
    #
    cH
    cdm
    cdm
    #
    @1
    cxp
    #
    @1
    cH
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    vz
    cv
    #
    cH
    co
    @4
    @5
    @7
    cH
    co
    #
    cH
    co
    wceq
    #
    vz
    @1
    wral
    #
    vy
    @1
    wral
    #
    vx
    @1
    wral
    #
    @6
    @5
    wceq
    @5
    @4
    cH
    co
    @5
    wceq
    wa
    #
    vy
    @1
    wral
    #
    vx
    @1
    wrex
    #
    w3a
    #
    cH
    cmndo
    wcel
    #
    @0
    @16
    cR
    c1st
    cfv
    #
    crn
    #
    @19
    cxp
    #
    @19
    cH
    wf
    #
    @9
    vz
    @19
    wral
    #
    vy
    @19
    wral
    #
    vx
    @19
    wral
    #
    @13
    vy
    @19
    wral
    #
    vx
    @19
    wrex
    #
    cR
    @18
    cH
    @19
    @18
    eqid
    #
    unmnd.1
    @19
    eqid
    #
    rngosm
    @0
    @9
    vx
    vy
    vz
    @19
    @19
    @19
    @4
    @5
    @7
    cR
    @18
    cH
    @19
    @27
    unmnd.1
    @28
    rngoass
    ralrimivvva
    @0
    @18
    cablo
    wcel
    @21
    wa
    @9
    @4
    @5
    @7
    @18
    co
    cH
    co
    @6
    @4
    @7
    cH
    co
    #
    @18
    co
    wceq
    @4
    @5
    @18
    co
    @7
    cH
    co
    @29
    @8
    @18
    co
    wceq
    w3a
    vz
    @19
    wral
    vy
    @19
    wral
    vx
    @19
    wral
    @26
    vx
    vy
    vz
    cR
    @18
    cH
    @19
    @27
    unmnd.1
    @28
    rngoi
    simprrd
    @0
    @19
    @1
    wceq
    @16
    @21
    @24
    @26
    w3a
    wb
    #
    cR
    @18
    cH
    unmnd.1
    @27
    rngorn1
    @30
    @1
    @19
    @1
    @19
    wceq
    #
    @3
    @21
    @12
    @24
    @15
    @26
    @2
    @20
    wceq
    #
    @31
    @3
    @21
    wb
    @32
    @31
    @1
    @19
    xpid11
    biimpri
    @2
    @1
    @20
    @19
    cH
    feq23
    mpancom
    @11
    @23
    vx
    @1
    @19
    @10
    @22
    vy
    @1
    @19
    @9
    vz
    @1
    @19
    raleq
    raleqbi1dv
    raleqbi1dv
    @14
    @25
    vx
    @1
    @19
    @13
    vy
    @1
    @19
    raleq
    rexeqbi1dv
    3anbi123d
    eqcoms
    syl
    mpbir3and
    cH
    cR
    c2nd
    cfv
    #
    wceq
    #
    cH
    cvv
    wcel
    #
    @17
    @16
    wb
    unmnd.1
    @34
    @35
    @33
    cvv
    wcel
    cR
    c2nd
    fvex
    cH
    @33
    cvv
    eleq1
    mpbiri
    vx
    vy
    vz
    cvv
    cH
    @1
    @1
    eqid
    ismndo1
    mp2b
    sylibr
end
