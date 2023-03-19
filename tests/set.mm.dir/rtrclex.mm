include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "ccom.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "cxp.mm"
include "ssun1.mm"
include "coundir.mm"
include "coundi.mm"
include "cossxp.mm"
include "ssun2.mm"
include "xpss12.mm"
include "mp2an.mm"
include "sstri.mm"
include "dmxpss.mm"
include "unssi.mm"
include "eqsstri.mm"
include "rnxpss.mm"
include "xpidtr.mm"
include "dmun.mm"
include "dmxpid.mm"
include "uneq2i.mm"
include "wceq.mm"
include "ssequn1.mm"
include "mpbi.mm"
include "eqtri.mm"
include "rnun.mm"
include "rnxpid.mm"
include "uneq12i.mm"
include "unidm.mm"
include "reseq2i.mm"
include "wfn.mm"
include "wrel.mm"
include "fnresi.mm"
include "fnrel.mm"
include "relssdmrn.mm"
include "mp2b.mm"
include "dmresi.mm"
include "rnresi.mm"
include "xpeq12i.mm"
include "sseqtri.mm"
include "pm3.2i.mm"
include "rtrclexlem.mm"
include "wi.mm"
include "id.mm"
include "coeq12d.mm"
include "sseq12d.mm"
include "dmeq.mm"
include "rneq.mm"
include "uneq12d.mm"
include "reseq2d.mm"
include "anbi12d.mm"
include "cleq2lem.mm"
include "biimprd.mm"
include "adantl.mm"
include "spcimedv.mm"
include "mp2ani.mm"
include "exsimpl.mm"
include "vex.mm"
include "ssex.mm"
include "exlimiv.mm"
include "syl.mm"
include "impbii.mm"
include "intexab.mm"
include "bitri.mm"

theorem rtrclex
  let vx: setvar x
  let cA: class A

  disjoint A x
  assert |- ( A e. _V <-> |^| { x | ( A C_ x /\ ( ( x o. x ) C_ x /\ ( _I |` ( dom x u. ran x ) ) C_ x ) ) } e. _V )

  proof
    cA
    cvv
    wcel
    #
    cA
    vx
    cv
    #
    wss
    #
    @1
    @1
    ccom
    #
    @1
    wss
    #
    cid
    @1
    cdm
    #
    @1
    crn
    #
    cun
    #
    cres
    #
    @1
    wss
    #
    wa
    #
    wa
    #
    vx
    wex
    #
    @11
    vx
    cab
    cint
    cvv
    wcel
    @0
    @12
    @0
    cA
    cA
    cA
    cdm
    #
    cA
    crn
    #
    cun
    #
    @15
    cxp
    #
    cun
    #
    wss
    #
    @17
    @17
    ccom
    #
    @17
    wss
    #
    cid
    @17
    cdm
    #
    @17
    crn
    #
    cun
    #
    cres
    #
    @17
    wss
    #
    wa
    #
    @12
    cA
    @16
    ssun1
    @20
    @25
    @19
    @16
    @17
    @19
    cA
    @17
    ccom
    #
    @16
    @17
    ccom
    #
    cun
    @16
    cA
    @16
    @17
    coundir
    @27
    @28
    @16
    @27
    cA
    cA
    ccom
    #
    cA
    @16
    ccom
    #
    cun
    @16
    cA
    cA
    @16
    coundi
    @29
    @30
    @16
    @29
    @13
    @14
    cxp
    #
    @16
    cA
    cA
    cossxp
    @13
    @15
    wss
    #
    @14
    @15
    wss
    #
    @31
    @16
    wss
    @13
    @14
    ssun1
    #
    @14
    @13
    ssun2
    #
    @13
    @15
    @14
    @15
    xpss12
    mp2an
    sstri
    @30
    @16
    cdm
    #
    @14
    cxp
    #
    @16
    cA
    @16
    cossxp
    @36
    @15
    wss
    @33
    @37
    @16
    wss
    @15
    @15
    dmxpss
    @35
    @36
    @15
    @14
    @15
    xpss12
    mp2an
    sstri
    unssi
    eqsstri
    @28
    @16
    cA
    ccom
    #
    @16
    @16
    ccom
    #
    cun
    @16
    @16
    cA
    @16
    coundi
    @38
    @39
    @16
    @38
    @13
    @16
    crn
    #
    cxp
    #
    @16
    @16
    cA
    cossxp
    @32
    @40
    @15
    wss
    @41
    @16
    wss
    @34
    @15
    @15
    rnxpss
    @13
    @15
    @40
    @15
    xpss12
    mp2an
    sstri
    @15
    xpidtr
    unssi
    eqsstri
    unssi
    eqsstri
    @16
    cA
    ssun2
    #
    sstri
    @24
    @16
    @17
    @24
    cid
    @15
    cres
    #
    @16
    @23
    @15
    cid
    @23
    @15
    @15
    cun
    @15
    @21
    @15
    @22
    @15
    @21
    @13
    @36
    cun
    #
    @15
    cA
    @16
    dmun
    @44
    @13
    @15
    cun
    #
    @15
    @36
    @15
    @13
    @15
    dmxpid
    uneq2i
    @32
    @45
    @15
    wceq
    @34
    @13
    @15
    ssequn1
    mpbi
    eqtri
    eqtri
    @22
    @14
    @40
    cun
    #
    @15
    cA
    @16
    rnun
    @46
    @14
    @15
    cun
    #
    @15
    @40
    @15
    @14
    @15
    rnxpid
    uneq2i
    @33
    @47
    @15
    wceq
    @35
    @14
    @15
    ssequn1
    mpbi
    eqtri
    eqtri
    uneq12i
    @15
    unidm
    eqtri
    reseq2i
    @43
    @43
    cdm
    #
    @43
    crn
    #
    cxp
    #
    @16
    @43
    @15
    wfn
    @43
    wrel
    @43
    @50
    wss
    @15
    fnresi
    @15
    @43
    fnrel
    @43
    relssdmrn
    mp2b
    @48
    @15
    @49
    @15
    @15
    dmresi
    @15
    rnresi
    xpeq12i
    sseqtri
    eqsstri
    @42
    sstri
    pm3.2i
    @0
    @11
    @18
    @26
    wa
    #
    vx
    @17
    cvv
    cA
    cvv
    rtrclexlem
    @1
    @17
    wceq
    #
    @51
    @11
    wi
    @0
    @52
    @11
    @51
    @10
    @26
    @1
    @17
    cA
    @52
    @4
    @20
    @9
    @25
    @52
    @3
    @19
    @1
    @17
    @52
    @1
    @17
    @1
    @17
    @52
    id
    #
    @53
    coeq12d
    @53
    sseq12d
    @52
    @8
    @24
    @1
    @17
    @52
    @7
    @23
    cid
    @52
    @5
    @21
    @6
    @22
    @1
    @17
    dmeq
    @1
    @17
    rneq
    uneq12d
    reseq2d
    @53
    sseq12d
    anbi12d
    cleq2lem
    biimprd
    adantl
    spcimedv
    mp2ani
    @12
    @2
    vx
    wex
    @0
    @2
    @10
    vx
    exsimpl
    @2
    @0
    vx
    cA
    @1
    vx
    vex
    ssex
    exlimiv
    syl
    impbii
    @11
    vx
    intexab
    bitri
end
