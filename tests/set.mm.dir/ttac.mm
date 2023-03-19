include "wac.mm"
include "ccrd.mm"
include "cdm.mm"
include "cvv.mm"
include "wceq.mm"
include "com.mm"
include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "cxp.mm"
include "cen.mm"
include "wi.mm"
include "wal.mm"
include "dfac10.mm"
include "wcel.mm"
include "vex.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "infxpidm2.mm"
include "ex.mm"
include "syl.mm"
include "alrimiv.mm"
include "cfn.mm"
include "finnum.mm"
include "adantl.mm"
include "wn.mm"
include "wa.mm"
include "char.mm"
include "cfv.mm"
include "cun.mm"
include "wss.mm"
include "con0.mm"
include "harcl.mm"
include "onenon.mm"
include "ax-mp.mm"
include "cwdom.mm"
include "fvex.mm"
include "unex.mm"
include "harinf.mm"
include "mpan.mm"
include "ssun1.mm"
include "syl6ss.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "breq2.mm"
include "xpeq12.mm"
include "anidms.mm"
include "id.mm"
include "breq12d.mm"
include "imbi12d.mm"
include "spcv.mm"
include "syl5.mm"
include "imp.mm"
include "wo.mm"
include "harndom.mm"
include "mp2.mm"
include "domtr.mm"
include "mto.mm"
include "unxpwdom2.mm"
include "orel2.mm"
include "wb.mm"
include "wdomnumr.mm"
include "sylib.mm"
include "numdom.mm"
include "sylancr.mm"
include "ssun2.mm"
include "ssnum.mm"
include "sylancl.mm"
include "pm2.61dan.mm"
include "eqv.mm"
include "sylibr.mm"
include "impbii.mm"
include "bitri.mm"

theorem ttac
  let vc: setvar c
  let va: setvar a


  assert |- ( CHOICE <-> A. c ( _om ~<_ c -> ( c X. c ) ~~ c ) )

  proof
    wac
    ccrd
    cdm
    #
    cvv
    wceq
    #
    com
    vc
    cv
    #
    cdom
    wbr
    #
    @2
    @2
    cxp
    #
    @2
    cen
    wbr
    #
    wi
    #
    vc
    wal
    #
    dfac10
    @1
    @7
    @1
    @6
    vc
    @1
    @2
    @0
    wcel
    #
    @6
    @1
    @8
    @2
    cvv
    wcel
    vc
    vex
    @0
    cvv
    @2
    eleq2
    mpbiri
    @8
    @3
    @5
    @2
    infxpidm2
    ex
    syl
    alrimiv
    @7
    va
    cv
    #
    @0
    wcel
    #
    va
    wal
    @1
    @7
    @10
    va
    @7
    @9
    cfn
    wcel
    #
    @10
    @11
    @10
    @7
    @9
    finnum
    adantl
    @7
    @11
    wn
    #
    wa
    #
    @9
    char
    cfv
    #
    @9
    cun
    #
    @0
    wcel
    #
    @9
    @15
    wss
    @10
    @13
    @14
    @0
    wcel
    #
    @15
    @14
    cdom
    wbr
    #
    @16
    @14
    con0
    wcel
    @17
    @9
    harcl
    @14
    onenon
    ax-mp
    #
    @13
    @15
    @14
    cwdom
    wbr
    #
    @18
    @13
    @15
    @15
    cxp
    #
    @15
    cen
    wbr
    #
    @20
    @7
    @12
    @22
    @12
    com
    @15
    cdom
    wbr
    #
    @7
    @22
    @15
    cvv
    wcel
    #
    @12
    com
    @15
    wss
    @23
    @14
    @9
    @9
    char
    fvex
    va
    vex
    #
    unex
    #
    @12
    com
    @14
    @15
    @9
    cvv
    wcel
    @12
    com
    @14
    wss
    @25
    @9
    cvv
    harinf
    mpan
    @14
    @9
    ssun1
    #
    syl6ss
    com
    @15
    cvv
    ssdomg
    mpsyl
    @6
    @23
    @22
    wi
    vc
    @15
    @26
    @2
    @15
    wceq
    #
    @3
    @23
    @5
    @22
    @2
    @15
    com
    cdom
    breq2
    @28
    @4
    @21
    @2
    @15
    cen
    @28
    @4
    @21
    wceq
    @2
    @15
    @2
    @15
    xpeq12
    anidms
    @28
    id
    breq12d
    imbi12d
    spcv
    syl5
    imp
    @15
    @9
    cdom
    wbr
    #
    wn
    @22
    @20
    @29
    wo
    @20
    @29
    @14
    @9
    cdom
    wbr
    #
    @9
    harndom
    @14
    @15
    cdom
    wbr
    #
    @29
    @30
    @24
    @14
    @15
    wss
    @31
    @26
    @27
    @14
    @15
    cvv
    ssdomg
    mp2
    @14
    @15
    @9
    domtr
    mpan
    mto
    @15
    @14
    @9
    unxpwdom2
    @29
    @20
    orel2
    mpsyl
    syl
    @17
    @20
    @18
    wb
    @19
    @15
    @14
    wdomnumr
    ax-mp
    sylib
    @14
    @15
    numdom
    sylancr
    @9
    @14
    ssun2
    @15
    @9
    ssnum
    sylancl
    pm2.61dan
    alrimiv
    va
    @0
    eqv
    sylibr
    impbii
    bitri
end
