include "cdm.mm"
include "wcel.mm"
include "wsmo.mm"
include "cres.mm"
include "con0.mm"
include "wf.mm"
include "word.mm"
include "cv.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "w3a.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wa.mm"
include "wfun.mm"
include "funres.mm"
include "funfn.mm"
include "3imtr3i.mm"
include "resss.mm"
include "rnss.mm"
include "ax-mp.mm"
include "sstr.mm"
include "mpan.mm"
include "anim12i.mm"
include "df-f.mm"
include "3imtr4i.mm"
include "a1i.mm"
include "cin.mm"
include "ordelord.mm"
include "expcom.mm"
include "ordin.mm"
include "ex.mm"
include "syli.mm"
include "wceq.mm"
include "wb.mm"
include "dmres.mm"
include "ordeq.mm"
include "syl6ibr.mm"
include "dmss.mm"
include "ssralv.mm"
include "ralimi.mm"
include "syl.mm"
include "inss1.mm"
include "eqsstri.mm"
include "simpl.mm"
include "sseldi.mm"
include "fvres.mm"
include "simpr.mm"
include "eleq12d.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "ralbiia.mm"
include "sylibr.mm"
include "3anim123d.mm"
include "df-smo.mm"
include "3imtr4g.mm"
include "impcom.mm"

theorem smores
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Smo A /\ B e. dom A ) -> Smo ( A |` B ) )

  proof
    cB
    cA
    cdm
    #
    wcel
    #
    cA
    wsmo
    #
    cA
    cB
    cres
    #
    wsmo
    #
    @1
    @0
    con0
    cA
    wf
    #
    @0
    word
    #
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    @7
    cA
    cfv
    #
    @8
    cA
    cfv
    #
    wcel
    #
    wi
    #
    vy
    @0
    wral
    #
    vx
    @0
    wral
    #
    w3a
    @3
    cdm
    #
    con0
    @3
    wf
    #
    @16
    word
    #
    @9
    @7
    @3
    cfv
    #
    @8
    @3
    cfv
    #
    wcel
    #
    wi
    #
    vy
    @16
    wral
    #
    vx
    @16
    wral
    #
    w3a
    @2
    @4
    @1
    @5
    @17
    @6
    @18
    @15
    @24
    @5
    @17
    wi
    @1
    cA
    @0
    wfn
    #
    cA
    crn
    #
    con0
    wss
    #
    wa
    @3
    @16
    wfn
    #
    @3
    crn
    #
    con0
    wss
    #
    wa
    @5
    @17
    @25
    @28
    @27
    @30
    cA
    wfun
    @3
    wfun
    @25
    @28
    cB
    cA
    funres
    cA
    funfn
    @3
    funfn
    3imtr3i
    @29
    @26
    wss
    #
    @27
    @30
    @3
    cA
    wss
    #
    @31
    cA
    cB
    resss
    #
    @3
    cA
    rnss
    ax-mp
    @29
    @26
    con0
    sstr
    mpan
    anim12i
    @0
    con0
    cA
    df-f
    @16
    con0
    @3
    df-f
    3imtr4i
    a1i
    @1
    @6
    cB
    @0
    cin
    #
    word
    #
    @18
    @6
    @1
    cB
    word
    #
    @35
    @6
    @1
    @36
    @0
    cB
    ordelord
    expcom
    @36
    @6
    @35
    cB
    @0
    ordin
    ex
    syli
    @16
    @34
    wceq
    @18
    @35
    wb
    cA
    cB
    dmres
    #
    @16
    @34
    ordeq
    ax-mp
    syl6ibr
    @15
    @24
    wi
    @1
    @15
    @13
    vy
    @16
    wral
    #
    vx
    @16
    wral
    #
    @24
    @15
    @14
    vx
    @16
    wral
    #
    @39
    @16
    @0
    wss
    #
    @15
    @40
    wi
    @32
    @41
    @33
    @3
    cA
    dmss
    ax-mp
    #
    @14
    vx
    @16
    @0
    ssralv
    ax-mp
    @14
    @38
    vx
    @16
    @41
    @14
    @38
    wi
    @42
    @13
    vy
    @16
    @0
    ssralv
    ax-mp
    ralimi
    syl
    @23
    @38
    vx
    @16
    @7
    @16
    wcel
    #
    @22
    @13
    vy
    @16
    @43
    @8
    @16
    wcel
    #
    wa
    #
    @21
    @12
    @9
    @45
    @19
    @10
    @20
    @11
    @45
    @7
    cB
    wcel
    @19
    @10
    wceq
    @45
    @16
    cB
    @7
    @16
    @34
    cB
    @37
    cB
    @0
    inss1
    eqsstri
    #
    @43
    @44
    simpl
    sseldi
    @7
    cB
    cA
    fvres
    syl
    @45
    @8
    cB
    wcel
    @20
    @11
    wceq
    @45
    @16
    cB
    @8
    @46
    @43
    @44
    simpr
    sseldi
    @8
    cB
    cA
    fvres
    syl
    eleq12d
    imbi2d
    ralbidva
    ralbiia
    sylibr
    a1i
    3anim123d
    vx
    vy
    cA
    df-smo
    vx
    vy
    @3
    df-smo
    3imtr4g
    impcom
end
