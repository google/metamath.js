include "con0.mm"
include "wcel.mm"
include "cr1.mm"
include "cdm.mm"
include "cima.mm"
include "cuni.mm"
include "crnk.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "word.mm"
include "wlim.mm"
include "wfun.mm"
include "r1funlim.mm"
include "simpri.mm"
include "limord.mm"
include "ax-mp.mm"
include "ordelon.mm"
include "mpan.mm"
include "cv.mm"
include "wi.mm"
include "eleq1.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "wral.mm"
include "wb.mm"
include "ordtr1.mm"
include "ancoms.mm"
include "pm5.5.mm"
include "syl.mm"
include "ralbidva.mm"
include "csuc.mm"
include "cpw.mm"
include "wss.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "eloni.mm"
include "ordelsuc.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "adantr.mm"
include "limsuc.mm"
include "sylib.mm"
include "simpll.mm"
include "r1ord3g.mm"
include "mpd.mm"
include "rankidb.mm"
include "ad2antrl.mm"
include "suceq.mm"
include "ad2antll.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "sseldd.mm"
include "ex.mm"
include "ralimdva.mm"
include "imp.mm"
include "dfss3.mm"
include "sylibr.mm"
include "vex.mm"
include "elpw.mm"
include "r1sucg.mm"
include "eleqtrrd.mm"
include "r1elwf.mm"
include "crab.mm"
include "cint.mm"
include "rankval3b.mm"
include "adantl.mm"
include "ralimi.mm"
include "ralbi.mm"
include "syl6bbr.mm"
include "rabbidv.mm"
include "inteqd.mm"
include "intmin.mm"
include "3eqtrd.mm"
include "jca.mm"
include "sylbid.mm"
include "com12.mm"
include "a1i.mm"
include "tfis3.mm"
include "mpcom.mm"

theorem rankonidlem
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. dom R1 -> ( A e. U. ( R1 " On ) /\ ( rank ` A ) = A ) )

  proof
    cA
    con0
    wcel
    #
    cA
    cr1
    cdm
    #
    wcel
    #
    cA
    cr1
    con0
    cima
    cuni
    #
    wcel
    #
    cA
    crnk
    cfv
    #
    cA
    wceq
    #
    wa
    #
    @1
    word
    #
    @2
    @0
    @1
    wlim
    #
    @8
    cr1
    wfun
    @9
    r1funlim
    simpri
    #
    @1
    limord
    ax-mp
    #
    @1
    cA
    ordelon
    mpan
    vx
    cv
    #
    @1
    wcel
    #
    @12
    @3
    wcel
    #
    @12
    crnk
    cfv
    #
    @12
    wceq
    #
    wa
    #
    wi
    #
    vy
    cv
    #
    @1
    wcel
    #
    @19
    @3
    wcel
    #
    @19
    crnk
    cfv
    #
    @19
    wceq
    #
    wa
    #
    wi
    #
    @2
    @7
    wi
    vx
    vy
    cA
    @12
    @19
    wceq
    #
    @13
    @20
    @17
    @24
    @12
    @19
    @1
    eleq1
    @26
    @14
    @21
    @16
    @23
    @12
    @19
    @3
    eleq1
    @26
    @15
    @22
    @12
    @19
    @12
    @19
    crnk
    fveq2
    @26
    id
    eqeq12d
    anbi12d
    imbi12d
    @12
    cA
    wceq
    #
    @13
    @2
    @17
    @7
    @12
    cA
    @1
    eleq1
    @27
    @14
    @4
    @16
    @6
    @12
    cA
    @3
    eleq1
    @27
    @15
    @5
    @12
    cA
    @12
    cA
    crnk
    fveq2
    @27
    id
    eqeq12d
    anbi12d
    imbi12d
    @25
    vy
    @12
    wral
    #
    @18
    wi
    @12
    con0
    wcel
    #
    @13
    @28
    @17
    @13
    @28
    @24
    vy
    @12
    wral
    #
    @17
    @13
    @25
    @24
    vy
    @12
    @13
    @19
    @12
    wcel
    #
    wa
    #
    @20
    @25
    @24
    wb
    @31
    @13
    @20
    @8
    @31
    @13
    wa
    @20
    wi
    @11
    @19
    @12
    @1
    ordtr1
    ax-mp
    ancoms
    #
    @20
    @24
    pm5.5
    syl
    ralbidva
    @13
    @30
    @17
    @13
    @30
    wa
    #
    @14
    @16
    @34
    @12
    @12
    csuc
    #
    cr1
    cfv
    #
    wcel
    @14
    @34
    @12
    @12
    cr1
    cfv
    #
    cpw
    #
    @36
    @34
    @12
    @37
    wss
    #
    @12
    @38
    wcel
    @34
    @19
    @37
    wcel
    #
    vy
    @12
    wral
    #
    @39
    @13
    @30
    @41
    @13
    @24
    @40
    vy
    @12
    @32
    @24
    @40
    @32
    @24
    wa
    #
    @19
    csuc
    #
    cr1
    cfv
    #
    @37
    @19
    @42
    @43
    @12
    wss
    #
    @44
    @37
    wss
    #
    @42
    @31
    @45
    @13
    @31
    @24
    simplr
    #
    @42
    @31
    @12
    word
    #
    @31
    @45
    wb
    @47
    @42
    @29
    @48
    @13
    @29
    @31
    @24
    @8
    @13
    @29
    @11
    @1
    @12
    ordelon
    mpan
    #
    ad2antrr
    @12
    eloni
    syl
    @19
    @12
    @12
    ordelsuc
    syl2anc
    mpbid
    @42
    @43
    @1
    wcel
    #
    @13
    @45
    @46
    wi
    @42
    @20
    @50
    @32
    @20
    @24
    @33
    adantr
    @9
    @20
    @50
    wb
    @10
    @1
    @19
    limsuc
    ax-mp
    sylib
    @13
    @31
    @24
    simpll
    @43
    @12
    r1ord3g
    syl2anc
    mpd
    @42
    @19
    @22
    csuc
    #
    cr1
    cfv
    #
    @44
    @21
    @19
    @52
    wcel
    @32
    @23
    @19
    rankidb
    ad2antrl
    @42
    @51
    @43
    cr1
    @23
    @51
    @43
    wceq
    @32
    @21
    @22
    @19
    suceq
    ad2antll
    fveq2d
    eleqtrd
    sseldd
    ex
    ralimdva
    imp
    vy
    @12
    @37
    dfss3
    sylibr
    @12
    @37
    vx
    vex
    elpw
    sylibr
    @13
    @36
    @38
    wceq
    @30
    @12
    r1sucg
    adantr
    eleqtrrd
    @12
    @35
    r1elwf
    syl
    #
    @34
    @15
    @22
    vz
    cv
    #
    wcel
    #
    vy
    @12
    wral
    #
    vz
    con0
    crab
    #
    cint
    #
    @12
    @54
    wss
    #
    vz
    con0
    crab
    #
    cint
    #
    @12
    @34
    @14
    @15
    @58
    wceq
    @53
    vz
    vy
    @12
    rankval3b
    syl
    @30
    @58
    @61
    wceq
    @13
    @30
    @57
    @60
    @30
    @56
    @59
    vz
    con0
    @30
    @56
    @19
    @54
    wcel
    #
    vy
    @12
    wral
    #
    @59
    @30
    @55
    @62
    wb
    #
    vy
    @12
    wral
    @56
    @63
    wb
    @24
    @64
    vy
    @12
    @23
    @64
    @21
    @22
    @19
    @54
    eleq1
    adantl
    ralimi
    @55
    @62
    vy
    @12
    ralbi
    syl
    vy
    @12
    @54
    dfss3
    syl6bbr
    rabbidv
    inteqd
    adantl
    @34
    @29
    @61
    @12
    wceq
    @13
    @29
    @30
    @49
    adantr
    vz
    @12
    con0
    intmin
    syl
    3eqtrd
    jca
    ex
    sylbid
    com12
    a1i
    tfis3
    mpcom
end
