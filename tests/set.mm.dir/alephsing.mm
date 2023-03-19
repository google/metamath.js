include "wlim.mm"
include "cvv.mm"
include "wcel.mm"
include "cale.mm"
include "cfv.mm"
include "ccf.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "wf.mm"
include "wsmo.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "w3a.mm"
include "wex.mm"
include "cres.mm"
include "wfun.mm"
include "con0.mm"
include "wfn.mm"
include "alephfnon.mm"
include "fnfun.mm"
include "ax-mp.mm"
include "simpl.mm"
include "resfunexg.mm"
include "sylancr.mm"
include "crn.mm"
include "limelon.mm"
include "onss.mm"
include "syl.mm"
include "fnssres.mm"
include "fvres.mm"
include "adantl.mm"
include "alephord2i.mm"
include "imp.mm"
include "eqeltrd.mm"
include "sylan.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "cdm.mm"
include "alephsmo.mm"
include "fndm.mm"
include "syl6eleqr.mm"
include "smores.mm"
include "ciun.mm"
include "alephlim.mm"
include "eleq2d.mm"
include "eliun.mm"
include "alephon.mm"
include "onelssi.mm"
include "reximi.mm"
include "sylbi.mm"
include "syl6bi.mm"
include "ralrimiv.mm"
include "feq1.mm"
include "smoeq.mm"
include "fveq1.mm"
include "sylan9eq.mm"
include "sseq2d.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "3anbi123d.mm"
include "spcegv.mm"
include "syl13anc.mm"
include "wi.mm"
include "cfcof.mm"
include "mpd.mm"
include "expcom.mm"
include "wn.mm"
include "c0.mm"
include "cf0.mm"
include "fvprc.mm"
include "fveq2d.mm"
include "3eqtr4a.mm"
include "pm2.61d1.mm"

theorem alephsing
  let cA: class A
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( Lim A -> ( cf ` ( aleph ` A ) ) = ( cf ` A ) )

  proof
    cA
    wlim
    #
    cA
    cvv
    wcel
    #
    cA
    cale
    cfv
    #
    ccf
    cfv
    #
    cA
    ccf
    cfv
    #
    wceq
    #
    @1
    @0
    @5
    @1
    @0
    wa
    #
    cA
    @2
    vf
    cv
    #
    wf
    #
    @7
    wsmo
    #
    vx
    cv
    #
    vy
    cv
    #
    @7
    cfv
    #
    wss
    #
    vy
    cA
    wrex
    #
    vx
    @2
    wral
    #
    w3a
    #
    vf
    wex
    #
    @5
    @6
    cale
    cA
    cres
    #
    cvv
    wcel
    #
    cA
    @2
    @18
    wf
    #
    @18
    wsmo
    #
    @10
    @11
    cale
    cfv
    #
    wss
    #
    vy
    cA
    wrex
    #
    vx
    @2
    wral
    #
    @17
    @6
    cale
    wfun
    #
    @1
    @19
    cale
    con0
    wfn
    #
    @26
    alephfnon
    con0
    cale
    fnfun
    ax-mp
    @1
    @0
    simpl
    cale
    cA
    cvv
    resfunexg
    sylancr
    @6
    @18
    cA
    wfn
    #
    @18
    crn
    @2
    wss
    #
    @20
    @6
    @27
    cA
    con0
    wss
    #
    @28
    alephfnon
    @6
    cA
    con0
    wcel
    #
    @30
    cA
    cvv
    limelon
    #
    cA
    onss
    syl
    con0
    cA
    cale
    fnssres
    sylancr
    #
    @6
    @28
    @11
    @18
    cfv
    #
    @2
    wcel
    #
    vy
    cA
    wral
    @29
    @33
    @6
    @35
    vy
    cA
    @6
    @31
    @11
    cA
    wcel
    #
    @35
    @32
    @31
    @36
    wa
    @34
    @22
    @2
    @36
    @34
    @22
    wceq
    @31
    @11
    cA
    cale
    fvres
    #
    adantl
    @31
    @36
    @22
    @2
    wcel
    @11
    cA
    alephord2i
    imp
    eqeltrd
    sylan
    ralrimiva
    vy
    cA
    @2
    @18
    fnfvrnss
    syl2anc
    cA
    @2
    @18
    df-f
    sylanbrc
    @6
    cale
    wsmo
    cA
    cale
    cdm
    #
    wcel
    @21
    alephsmo
    @6
    cA
    con0
    @38
    @32
    @27
    @38
    con0
    wceq
    alephfnon
    con0
    cale
    fndm
    ax-mp
    syl6eleqr
    cale
    cA
    smores
    sylancr
    @6
    @24
    vx
    @2
    @6
    @10
    @2
    wcel
    @10
    vy
    cA
    @22
    ciun
    #
    wcel
    #
    @24
    @6
    @2
    @39
    @10
    vy
    cA
    cvv
    alephlim
    eleq2d
    @40
    @10
    @22
    wcel
    #
    vy
    cA
    wrex
    @24
    vy
    @10
    cA
    @22
    eliun
    @41
    @23
    vy
    cA
    @22
    @10
    @11
    alephon
    onelssi
    reximi
    sylbi
    syl6bi
    ralrimiv
    @19
    @20
    @21
    @25
    w3a
    #
    @17
    @16
    @42
    vf
    @18
    cvv
    @7
    @18
    wceq
    #
    @8
    @20
    @9
    @21
    @15
    @25
    cA
    @2
    @7
    @18
    feq1
    @7
    @18
    smoeq
    @43
    @14
    @24
    vx
    @2
    @43
    @13
    @23
    vy
    cA
    @43
    @36
    wa
    @12
    @22
    @10
    @43
    @36
    @12
    @34
    @22
    @11
    @7
    @18
    fveq1
    @37
    sylan9eq
    sseq2d
    rexbidva
    ralbidv
    3anbi123d
    spcegv
    imp
    syl13anc
    @6
    @2
    con0
    wcel
    @31
    @17
    @5
    wi
    cA
    alephon
    @32
    vx
    vy
    @2
    cA
    vf
    cfcof
    sylancr
    mpd
    expcom
    @1
    wn
    #
    c0
    ccf
    cfv
    c0
    @3
    @4
    cf0
    @44
    @2
    c0
    ccf
    cA
    cale
    fvprc
    fveq2d
    cA
    ccf
    fvprc
    3eqtr4a
    pm2.61d1
end
