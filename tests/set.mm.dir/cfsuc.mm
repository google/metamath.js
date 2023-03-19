include "con0.mm"
include "wcel.mm"
include "csuc.mm"
include "ccf.mm"
include "cfv.mm"
include "cv.mm"
include "ccrd.mm"
include "wceq.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "c1o.mm"
include "sucelon.mm"
include "cfval.mm"
include "sylbi.mm"
include "wn.mm"
include "csn.mm"
include "cardsn.mm"
include "eqcomd.mm"
include "snidg.mm"
include "wo.mm"
include "elsuci.mm"
include "onelss.mm"
include "wi.mm"
include "eqimss.mm"
include "a1i.mm"
include "jaod.mm"
include "syl5.mm"
include "sseq2.mm"
include "rspcev.mm"
include "syl6an.mm"
include "ralrimiv.mm"
include "cun.mm"
include "ssun2.mm"
include "df-suc.mm"
include "sseqtr4i.mm"
include "jctil.mm"
include "snex.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "sseq1.mm"
include "rexeq.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "spcev.mm"
include "syl2anc.mm"
include "1on.mm"
include "elexi.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "elab.mm"
include "sylibr.mm"
include "c0.mm"
include "el1o.mm"
include "eqcom.mm"
include "cdm.mm"
include "wb.mm"
include "cvv.mm"
include "vex.mm"
include "onssnum.mm"
include "mpan.mm"
include "cardnueq0.mm"
include "syl.mm"
include "syl5bb.mm"
include "biimpa.mm"
include "rex0.mm"
include "nrex.mm"
include "wne.mm"
include "nsuceq0.mm"
include "r19.2z.mm"
include "mto.mm"
include "mtbiri.mm"
include "intnand.mm"
include "imnan.mm"
include "mpbi.mm"
include "w3a.mm"
include "suceloni.mm"
include "onss.mm"
include "sstr.mm"
include "sylan2.mm"
include "ancoms.mm"
include "adantrr.mm"
include "3adant2.mm"
include "simp2.mm"
include "simp3.mm"
include "jca31.mm"
include "3expib.mm"
include "mtoi.mm"
include "nexdv.mm"
include "0ex.mm"
include "sylnibr.mm"
include "adantr.mm"
include "eleq1.mm"
include "adantl.mm"
include "mtbird.mm"
include "sylan2b.mm"
include "ralrimiva.mm"
include "cardon.mm"
include "mpbiri.mm"
include "exlimiv.mm"
include "abssi.mm"
include "oneqmini.mm"
include "ax-mp.mm"
include "eqtr4d.mm"

theorem cfsuc
  let cA: class A
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v


  assert |- ( A e. On -> ( cf ` suc A ) = 1o )

  proof
    cA
    con0
    wcel
    #
    cA
    csuc
    #
    ccf
    cfv
    #
    vx
    cv
    #
    vy
    cv
    #
    ccrd
    cfv
    #
    wceq
    #
    @4
    @1
    wss
    #
    vz
    cv
    #
    vw
    cv
    #
    wss
    #
    vw
    @4
    wrex
    #
    vz
    @1
    wral
    #
    wa
    #
    wa
    #
    vy
    wex
    #
    vx
    cab
    #
    cint
    #
    c1o
    @0
    @1
    con0
    wcel
    #
    @2
    @17
    wceq
    cA
    sucelon
    vx
    vy
    vz
    vw
    @1
    cfval
    sylbi
    @0
    c1o
    @16
    wcel
    #
    vv
    cv
    #
    @16
    wcel
    #
    wn
    #
    vv
    c1o
    wral
    #
    c1o
    @17
    wceq
    #
    @0
    c1o
    @5
    wceq
    #
    @13
    wa
    #
    vy
    wex
    #
    @19
    @0
    c1o
    cA
    csn
    #
    ccrd
    cfv
    #
    wceq
    #
    @28
    @1
    wss
    #
    @10
    vw
    @28
    wrex
    #
    vz
    @1
    wral
    #
    wa
    #
    @27
    @0
    @29
    c1o
    cA
    con0
    cardsn
    eqcomd
    @0
    @33
    @31
    @0
    @32
    vz
    @1
    @0
    cA
    @28
    wcel
    @8
    @1
    wcel
    #
    @8
    cA
    wss
    #
    @32
    cA
    con0
    snidg
    @35
    @8
    cA
    wcel
    #
    @8
    cA
    wceq
    #
    wo
    @0
    @36
    @8
    cA
    elsuci
    @0
    @37
    @36
    @38
    cA
    @8
    onelss
    @38
    @36
    wi
    @0
    @8
    cA
    eqimss
    a1i
    jaod
    syl5
    @10
    @36
    vw
    cA
    @28
    @9
    cA
    @8
    sseq2
    rspcev
    syl6an
    ralrimiv
    @28
    cA
    @28
    cun
    @1
    @28
    cA
    ssun2
    cA
    df-suc
    sseqtr4i
    jctil
    @26
    @30
    @34
    wa
    vy
    @28
    cA
    snex
    @4
    @28
    wceq
    #
    @25
    @30
    @13
    @34
    @39
    @5
    @29
    c1o
    @4
    @28
    ccrd
    fveq2
    eqeq2d
    @39
    @7
    @31
    @12
    @33
    @4
    @28
    @1
    sseq1
    @39
    @11
    @32
    vz
    @1
    @10
    vw
    @4
    @28
    rexeq
    ralbidv
    anbi12d
    anbi12d
    spcev
    syl2anc
    @15
    @27
    vx
    c1o
    c1o
    con0
    1on
    elexi
    @3
    c1o
    wceq
    #
    @14
    @26
    vy
    @40
    @6
    @25
    @13
    @3
    c1o
    @5
    eqeq1
    anbi1d
    exbidv
    elab
    sylibr
    @0
    @22
    vv
    c1o
    @20
    c1o
    wcel
    @0
    @20
    c0
    wceq
    #
    @22
    @20
    el1o
    @0
    @41
    wa
    @21
    c0
    @16
    wcel
    #
    @0
    @42
    wn
    @41
    @0
    c0
    @5
    wceq
    #
    @13
    wa
    #
    vy
    wex
    #
    @42
    @0
    @44
    vy
    @0
    @44
    @4
    con0
    wss
    #
    @43
    wa
    #
    @13
    wa
    #
    @47
    @13
    wn
    wi
    @48
    wn
    @47
    @12
    @7
    @47
    @4
    c0
    wceq
    #
    @12
    wn
    @46
    @43
    @49
    @43
    @5
    c0
    wceq
    #
    @46
    @49
    c0
    @5
    eqcom
    @46
    @4
    ccrd
    cdm
    wcel
    #
    @50
    @49
    wb
    @4
    cvv
    wcel
    @46
    @51
    vy
    vex
    @4
    cvv
    onssnum
    mpan
    @4
    cardnueq0
    syl
    syl5bb
    biimpa
    @49
    @12
    @10
    vw
    c0
    wrex
    #
    vz
    @1
    wral
    #
    @53
    @52
    vz
    @1
    wrex
    #
    @52
    vz
    @1
    @52
    wn
    @35
    @10
    vw
    rex0
    a1i
    nrex
    @1
    c0
    wne
    @53
    @54
    cA
    nsuceq0
    @52
    vz
    @1
    r19.2z
    mpan
    mto
    @49
    @11
    @52
    vz
    @1
    @10
    vw
    @4
    c0
    rexeq
    ralbidv
    mtbiri
    syl
    intnand
    @47
    @13
    imnan
    mpbi
    @0
    @43
    @13
    @48
    @0
    @43
    @13
    w3a
    @46
    @43
    @13
    @0
    @13
    @46
    @43
    @0
    @7
    @46
    @12
    @7
    @0
    @46
    @0
    @7
    @18
    @46
    cA
    suceloni
    @18
    @7
    @1
    con0
    wss
    @46
    @1
    onss
    @4
    @1
    con0
    sstr
    sylan2
    sylan2
    ancoms
    adantrr
    3adant2
    @0
    @43
    @13
    simp2
    @0
    @43
    @13
    simp3
    jca31
    3expib
    mtoi
    nexdv
    @15
    @45
    vx
    c0
    0ex
    @3
    c0
    wceq
    #
    @14
    @44
    vy
    @55
    @6
    @43
    @13
    @3
    c0
    @5
    eqeq1
    anbi1d
    exbidv
    elab
    sylnibr
    adantr
    @41
    @21
    @42
    wb
    @0
    @20
    c0
    @16
    eleq1
    adantl
    mtbird
    sylan2b
    ralrimiva
    @16
    con0
    wss
    @19
    @23
    wa
    @24
    wi
    @15
    vx
    con0
    @14
    @3
    con0
    wcel
    #
    vy
    @6
    @56
    @13
    @6
    @56
    @5
    con0
    wcel
    @4
    cardon
    @3
    @5
    con0
    eleq1
    mpbiri
    adantr
    exlimiv
    abssi
    vv
    c1o
    @16
    oneqmini
    ax-mp
    syl2anc
    eqtr4d
end
