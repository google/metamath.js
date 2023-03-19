include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "cale.mm"
include "cfv.mm"
include "ccf.mm"
include "wceq.mm"
include "wn.mm"
include "csdm.mm"
include "wbr.mm"
include "alephordilem1.mm"
include "wa.mm"
include "cdom.mm"
include "cxp.mm"
include "cv.mm"
include "wf1.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wex.mm"
include "alephon.mm"
include "cff1.mm"
include "ax-mp.mm"
include "ciun.mm"
include "cvv.mm"
include "fvex.mm"
include "sucex.mm"
include "iunex.mm"
include "wf.mm"
include "f1f.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "wb.mm"
include "oneli.mm"
include "ffvelrn.mm"
include "onelon.mm"
include "sylancr.mm"
include "onsssuc.mm"
include "sylan2.mm"
include "anassrs.mm"
include "rexbidva.mm"
include "eliun.mm"
include "syl6bbr.mm"
include "ancoms.mm"
include "ralbidva.mm"
include "dfss3.mm"
include "biimpa.mm"
include "syl2anc.mm"
include "ssdomg.mm"
include "mpsyl.mm"
include "simprl.mm"
include "suceloni.mm"
include "wlim.mm"
include "alephislim.mm"
include "limsuc.mm"
include "sylbi.mm"
include "syl.mm"
include "breq1.mm"
include "ccrd.mm"
include "alephcard.mm"
include "iscard.mm"
include "simprbi.mm"
include "vtoclri.mm"
include "alephsucdom.mm"
include "syl5ibr.mm"
include "sylbid.mm"
include "syl5.mm"
include "expdimp.mm"
include "ralrimiv.mm"
include "iundom.mm"
include "domtr.mm"
include "expcom.mm"
include "exlimdv.mm"
include "mpi.mm"
include "cen.mm"
include "com.mm"
include "alephgeom.mm"
include "infxpen.mm"
include "mpan.mm"
include "xpdom1.mm"
include "syl6.mm"
include "domentr.mm"
include "sylsyld.mm"
include "imp.mm"
include "domnsym.mm"
include "ex.mm"
include "mt2d.mm"
include "wo.mm"
include "cfon.mm"
include "cfle.mm"
include "onsseleq.mm"
include "mpbii.mm"
include "mp2an.mm"
include "ori.mm"
include "c0.mm"
include "cf0.mm"
include "cdm.mm"
include "wfn.mm"
include "alephfnon.mm"
include "fndm.mm"
include "eleq2i.mm"
include "sucelon.mm"
include "bitr4i.mm"
include "ndmfv.mm"
include "sylnbir.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem alephreg
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( cf ` ( aleph ` suc A ) ) = ( aleph ` suc A )

  proof
    cA
    con0
    wcel
    #
    cA
    csuc
    #
    cale
    cfv
    #
    ccf
    cfv
    #
    @2
    wceq
    #
    @0
    @3
    @2
    wcel
    #
    wn
    @4
    @0
    @5
    cA
    cale
    cfv
    #
    @2
    csdm
    wbr
    #
    cA
    alephordilem1
    @0
    @5
    @7
    wn
    #
    @0
    @5
    wa
    #
    @2
    @6
    cdom
    wbr
    #
    @8
    @9
    @2
    @3
    @6
    cxp
    #
    cdom
    wbr
    #
    @11
    @6
    cdom
    wbr
    #
    @10
    @9
    @3
    @2
    vf
    cv
    #
    wf1
    #
    vx
    cv
    #
    vy
    cv
    #
    @14
    cfv
    #
    wss
    #
    vy
    @3
    wrex
    #
    vx
    @2
    wral
    #
    wa
    #
    vf
    wex
    #
    @12
    @2
    con0
    wcel
    #
    @23
    @1
    alephon
    #
    vx
    vy
    @2
    vf
    cff1
    ax-mp
    @9
    @22
    @12
    vf
    @22
    @9
    @12
    @22
    @9
    wa
    #
    @2
    vy
    @3
    @18
    csuc
    #
    ciun
    #
    cdom
    wbr
    #
    @28
    @11
    cdom
    wbr
    #
    @12
    @28
    cvv
    wcel
    @26
    @2
    @28
    wss
    #
    @29
    vy
    @3
    @27
    @2
    ccf
    fvex
    #
    @18
    @17
    @14
    fvex
    sucex
    iunex
    @26
    @3
    @2
    @14
    wf
    #
    @21
    @31
    @15
    @33
    @21
    @9
    @3
    @2
    @14
    f1f
    ad2antrr
    #
    @15
    @21
    @9
    simplr
    @33
    @21
    @31
    @33
    @21
    @16
    @28
    wcel
    #
    vx
    @2
    wral
    @31
    @33
    @20
    @35
    vx
    @2
    @16
    @2
    wcel
    @33
    @16
    con0
    wcel
    #
    @20
    @35
    wb
    #
    @2
    @16
    @25
    oneli
    @36
    @33
    @37
    @36
    @33
    wa
    #
    @20
    @16
    @27
    wcel
    #
    vy
    @3
    wrex
    @35
    @38
    @19
    @39
    vy
    @3
    @36
    @33
    @17
    @3
    wcel
    #
    @19
    @39
    wb
    #
    @33
    @40
    wa
    #
    @36
    @18
    con0
    wcel
    #
    @41
    @42
    @24
    @18
    @2
    wcel
    #
    @43
    @25
    @3
    @2
    @17
    @14
    ffvelrn
    #
    @2
    @18
    onelon
    sylancr
    @16
    @18
    onsssuc
    sylan2
    anassrs
    rexbidva
    vy
    @16
    @3
    @27
    eliun
    syl6bbr
    ancoms
    sylan2
    ralbidva
    vx
    @2
    @28
    dfss3
    syl6bbr
    biimpa
    syl2anc
    @2
    @28
    cvv
    ssdomg
    mpsyl
    @26
    @0
    @33
    @30
    @22
    @0
    @5
    simprl
    @34
    @0
    @33
    wa
    #
    @3
    cvv
    wcel
    @27
    @6
    cdom
    wbr
    #
    vy
    @3
    wral
    @30
    @32
    @46
    @47
    vy
    @3
    @0
    @33
    @40
    @47
    @42
    @44
    @0
    @47
    @45
    @0
    @44
    @27
    @2
    wcel
    #
    @47
    @0
    @1
    con0
    wcel
    #
    @44
    @48
    wb
    #
    cA
    suceloni
    @49
    @2
    wlim
    @50
    @1
    alephislim
    @2
    @18
    limsuc
    sylbi
    syl
    @48
    @47
    @0
    @27
    @2
    csdm
    wbr
    #
    vz
    cv
    #
    @2
    csdm
    wbr
    #
    @51
    vz
    @27
    @2
    @52
    @27
    @2
    csdm
    breq1
    @2
    ccrd
    cfv
    @2
    wceq
    #
    @53
    vz
    @2
    wral
    #
    @1
    alephcard
    @54
    @24
    @55
    vz
    @2
    iscard
    simprbi
    ax-mp
    #
    vtoclri
    @27
    cA
    alephsucdom
    syl5ibr
    sylbid
    syl5
    expdimp
    ralrimiv
    vy
    @3
    @6
    @27
    cvv
    iundom
    sylancr
    syl2anc
    @2
    @28
    @11
    domtr
    syl2anc
    expcom
    exlimdv
    mpi
    @0
    @5
    @13
    @0
    @6
    @6
    cxp
    #
    @6
    cen
    wbr
    #
    @5
    @11
    @57
    cdom
    wbr
    #
    @13
    @0
    com
    @6
    wss
    #
    @58
    cA
    alephgeom
    @6
    con0
    wcel
    @60
    @58
    cA
    alephon
    @6
    infxpen
    mpan
    sylbi
    @0
    @5
    @3
    @6
    cdom
    wbr
    #
    @59
    @5
    @61
    @0
    @3
    @2
    csdm
    wbr
    #
    @53
    @62
    vz
    @3
    @2
    @52
    @3
    @2
    csdm
    breq1
    @56
    vtoclri
    @3
    cA
    alephsucdom
    syl5ibr
    @3
    @6
    @6
    cA
    cale
    fvex
    xpdom1
    syl6
    @59
    @58
    @13
    @11
    @57
    @6
    domentr
    expcom
    sylsyld
    imp
    @2
    @11
    @6
    domtr
    syl2anc
    @2
    @6
    domnsym
    syl
    ex
    mt2d
    @5
    @4
    @3
    con0
    wcel
    #
    @24
    @5
    @4
    wo
    #
    @2
    cfon
    @25
    @63
    @24
    wa
    @3
    @2
    wss
    @64
    @2
    cfle
    @3
    @2
    onsseleq
    mpbii
    mp2an
    ori
    syl
    @0
    wn
    #
    c0
    ccf
    cfv
    c0
    @3
    @2
    cf0
    @65
    @2
    c0
    ccf
    @0
    @1
    cale
    cdm
    #
    wcel
    #
    @2
    c0
    wceq
    @67
    @49
    @0
    @66
    con0
    @1
    cale
    con0
    wfn
    @66
    con0
    wceq
    alephfnon
    con0
    cale
    fndm
    ax-mp
    eleq2i
    cA
    sucelon
    bitr4i
    @1
    cale
    ndmfv
    sylnbir
    #
    fveq2d
    @68
    3eqtr4a
    pm2.61i
end
