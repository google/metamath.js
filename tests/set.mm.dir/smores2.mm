include "wsmo.mm"
include "word.mm"
include "wa.mm"
include "cres.mm"
include "cdm.mm"
include "con0.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wfun.mm"
include "dfsmo2.mm"
include "simp1bi.mm"
include "ffun.mm"
include "syl.mm"
include "funres.mm"
include "funfn.mm"
include "sylib.mm"
include "cima.mm"
include "df-ima.mm"
include "imassrn.mm"
include "eqsstr3i.mm"
include "frn.mm"
include "syl5ss.mm"
include "df-f.mm"
include "sylanbrc.mm"
include "adantr.mm"
include "smodm.mm"
include "cin.mm"
include "ordin.mm"
include "wceq.mm"
include "wb.mm"
include "dmres.mm"
include "ordeq.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "ancoms.mm"
include "sylan.mm"
include "resss.mm"
include "dmss.mm"
include "simp3bi.mm"
include "ssralv.mm"
include "mpsyl.mm"
include "wel.mm"
include "wi.mm"
include "ordtr1.mm"
include "inss1.mm"
include "eqsstri.mm"
include "sseli.mm"
include "syl6.mm"
include "expcomd.mm"
include "imp31.mm"
include "fvres.mm"
include "ad2antlr.mm"
include "eleq12d.mm"
include "ralbidva.mm"
include "mpbird.mm"
include "syl3anbrc.mm"

theorem smores2
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Smo F /\ Ord A ) -> Smo ( F |` A ) )

  proof
    cF
    wsmo
    #
    cA
    word
    #
    wa
    #
    cF
    cA
    cres
    #
    cdm
    #
    con0
    @3
    wf
    #
    @4
    word
    #
    vy
    cv
    #
    @3
    cfv
    #
    vx
    cv
    #
    @3
    cfv
    #
    wcel
    #
    vy
    @9
    wral
    #
    vx
    @4
    wral
    #
    @3
    wsmo
    @0
    @5
    @1
    @0
    @3
    @4
    wfn
    #
    @3
    crn
    #
    con0
    wss
    @5
    @0
    cF
    wfun
    #
    @14
    @0
    cF
    cdm
    #
    con0
    cF
    wf
    #
    @16
    @0
    @18
    @17
    word
    #
    @7
    cF
    cfv
    #
    @9
    cF
    cfv
    #
    wcel
    #
    vy
    @9
    wral
    #
    vx
    @17
    wral
    #
    vx
    vy
    cF
    dfsmo2
    #
    simp1bi
    #
    @17
    con0
    cF
    ffun
    syl
    @16
    @3
    wfun
    @14
    cA
    cF
    funres
    @3
    funfn
    sylib
    syl
    @0
    @15
    cF
    crn
    #
    con0
    @15
    cF
    cA
    cima
    @27
    cF
    cA
    df-ima
    cF
    cA
    imassrn
    eqsstr3i
    @0
    @18
    @27
    con0
    wss
    @26
    @17
    con0
    cF
    frn
    syl
    syl5ss
    @4
    con0
    @3
    df-f
    sylanbrc
    adantr
    @0
    @19
    @1
    @6
    cF
    smodm
    @1
    @19
    @6
    @1
    @19
    wa
    cA
    @17
    cin
    #
    word
    #
    @6
    cA
    @17
    ordin
    @4
    @28
    wceq
    @6
    @29
    wb
    cF
    cA
    dmres
    #
    @4
    @28
    ordeq
    ax-mp
    sylibr
    ancoms
    sylan
    #
    @2
    @13
    @23
    vx
    @4
    wral
    #
    @0
    @32
    @1
    @4
    @17
    wss
    #
    @0
    @24
    @32
    @3
    cF
    wss
    @33
    cF
    cA
    resss
    @3
    cF
    dmss
    ax-mp
    @0
    @18
    @19
    @24
    @25
    simp3bi
    @23
    vx
    @4
    @17
    ssralv
    mpsyl
    adantr
    @2
    @12
    @23
    vx
    @4
    @2
    @9
    @4
    wcel
    #
    wa
    #
    @11
    @22
    vy
    @9
    @35
    vy
    vx
    wel
    #
    wa
    #
    @8
    @20
    @10
    @21
    @37
    @7
    cA
    wcel
    #
    @8
    @20
    wceq
    @2
    @34
    @36
    @38
    @2
    @36
    @34
    @38
    @2
    @36
    @34
    wa
    #
    @7
    @4
    wcel
    #
    @38
    @2
    @6
    @39
    @40
    wi
    @31
    @7
    @9
    @4
    ordtr1
    syl
    @4
    cA
    @7
    @4
    @28
    cA
    @30
    cA
    @17
    inss1
    eqsstri
    #
    sseli
    syl6
    expcomd
    imp31
    @7
    cA
    cF
    fvres
    syl
    @34
    @10
    @21
    wceq
    #
    @2
    @36
    @34
    @9
    cA
    wcel
    @42
    @4
    cA
    @9
    @41
    sseli
    @9
    cA
    cF
    fvres
    syl
    ad2antlr
    eleq12d
    ralbidva
    ralbidva
    mpbird
    vx
    vy
    @3
    dfsmo2
    syl3anbrc
end
