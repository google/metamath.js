include "con0.mm"
include "wcel.mm"
include "ccf.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "ccrd.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "cint.mm"
include "cfval.mm"
include "eqeq1d.mm"
include "wb.mm"
include "vex.mm"
include "eqeq1.mm"
include "anbi1d.mm"
include "exbidv.mm"
include "elab.mm"
include "fveq2.mm"
include "cardidm.mm"
include "syl6eq.mm"
include "eqeq2.mm"
include "mpbird.mm"
include "adantr.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "cardon.mm"
include "syl6eqelr.mm"
include "ssriv.mm"
include "onint0.mm"
include "ax-mp.mm"
include "0ex.mm"
include "w3a.mm"
include "onss.mm"
include "sstr.mm"
include "ancoms.mm"
include "sylan.mm"
include "3adant2.mm"
include "3adant3r.mm"
include "simp2.mm"
include "simp3.mm"
include "eqcom.mm"
include "cdm.mm"
include "cvv.mm"
include "onssnum.mm"
include "mpan.mm"
include "cardnueq0.mm"
include "syl.mm"
include "syl5bb.mm"
include "biimpa.mm"
include "sseq1.mm"
include "rexeq.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "wne.mm"
include "wn.mm"
include "rex0.mm"
include "rgenw.mm"
include "r19.2z.mm"
include "mpan2.mm"
include "rexnal.mm"
include "sylib.mm"
include "necon4ai.mm"
include "adantl.mm"
include "syl21anc.mm"
include "3expib.mm"
include "exlimdv.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "cf0.mm"
include "impbid1.mm"

theorem cfeq0
  let cA: class A
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. On -> ( ( cf ` A ) = (/) <-> A = (/) ) )

  proof
    cA
    con0
    wcel
    #
    cA
    ccf
    cfv
    #
    c0
    wceq
    #
    cA
    c0
    wceq
    #
    @0
    @2
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
    @5
    cA
    wss
    #
    vz
    cv
    vw
    cv
    wss
    #
    vw
    @5
    wrex
    #
    vz
    cA
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
    c0
    wceq
    #
    @3
    @0
    @1
    @16
    c0
    vx
    vy
    vz
    vw
    cA
    cfval
    eqeq1d
    @17
    c0
    @15
    wcel
    #
    @0
    @3
    @15
    con0
    wss
    @17
    @18
    wb
    vv
    @15
    con0
    vv
    cv
    #
    @15
    wcel
    #
    @19
    @19
    ccrd
    cfv
    #
    con0
    @20
    @19
    @6
    wceq
    #
    @12
    wa
    #
    vy
    wex
    #
    @21
    @19
    wceq
    #
    @14
    @24
    vx
    @19
    vv
    vex
    @4
    @19
    wceq
    #
    @13
    @23
    vy
    @26
    @7
    @22
    @12
    @4
    @19
    @6
    eqeq1
    anbi1d
    exbidv
    elab
    @23
    @25
    vy
    @22
    @25
    @12
    @22
    @25
    @21
    @6
    wceq
    @22
    @21
    @6
    ccrd
    cfv
    @6
    @19
    @6
    ccrd
    fveq2
    @5
    cardidm
    syl6eq
    @19
    @6
    @21
    eqeq2
    mpbird
    adantr
    exlimiv
    sylbi
    @19
    cardon
    syl6eqelr
    ssriv
    @15
    onint0
    ax-mp
    @18
    c0
    @6
    wceq
    #
    @12
    wa
    #
    vy
    wex
    #
    @0
    @3
    @14
    @29
    vx
    c0
    0ex
    @4
    c0
    wceq
    #
    @13
    @28
    vy
    @30
    @7
    @27
    @12
    @4
    c0
    @6
    eqeq1
    anbi1d
    exbidv
    elab
    @0
    @28
    @3
    vy
    @0
    @27
    @12
    @3
    @0
    @27
    @12
    w3a
    @5
    con0
    wss
    #
    @27
    @12
    @3
    @0
    @27
    @8
    @31
    @11
    @0
    @8
    @31
    @27
    @0
    cA
    con0
    wss
    #
    @8
    @31
    cA
    onss
    @8
    @32
    @31
    @5
    cA
    con0
    sstr
    ancoms
    sylan
    3adant2
    3adant3r
    @0
    @27
    @12
    simp2
    @0
    @27
    @12
    simp3
    @31
    @27
    wa
    #
    @12
    wa
    c0
    cA
    wss
    #
    @9
    vw
    c0
    wrex
    #
    vz
    cA
    wral
    #
    wa
    #
    @3
    @33
    @5
    c0
    wceq
    #
    @12
    @37
    @31
    @27
    @38
    @27
    @6
    c0
    wceq
    #
    @31
    @38
    c0
    @6
    eqcom
    @31
    @5
    ccrd
    cdm
    wcel
    #
    @39
    @38
    wb
    @5
    cvv
    wcel
    @31
    @40
    vy
    vex
    @5
    cvv
    onssnum
    mpan
    @5
    cardnueq0
    syl
    syl5bb
    biimpa
    @38
    @12
    @37
    @38
    @8
    @34
    @11
    @36
    @5
    c0
    cA
    sseq1
    @38
    @10
    @35
    vz
    cA
    @9
    vw
    @5
    c0
    rexeq
    ralbidv
    anbi12d
    biimpa
    sylan
    @36
    @3
    @34
    @36
    cA
    c0
    cA
    c0
    wne
    #
    @35
    wn
    #
    vz
    cA
    wrex
    #
    @36
    wn
    @41
    @42
    vz
    cA
    wral
    @43
    @42
    vz
    cA
    @9
    vw
    rex0
    rgenw
    @42
    vz
    cA
    r19.2z
    mpan2
    @35
    vz
    cA
    rexnal
    sylib
    necon4ai
    adantl
    syl
    syl21anc
    3expib
    exlimdv
    syl5bi
    syl5bi
    sylbid
    @3
    @1
    c0
    ccf
    cfv
    c0
    cA
    c0
    ccf
    fveq2
    cf0
    syl6eq
    impbid1
end
