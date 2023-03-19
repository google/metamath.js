include "cgru.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wa.mm"
include "cint.mm"
include "cvv.mm"
include "wcel.mm"
include "wtr.mm"
include "cv.mm"
include "cpw.mm"
include "cpr.mm"
include "wral.mm"
include "crn.mm"
include "cuni.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "simpr.mm"
include "intex.mm"
include "sylib.mm"
include "dfss3.mm"
include "grutr.mm"
include "ralimi.mm"
include "sylbi.mm"
include "trint.mm"
include "syl.mm"
include "adantr.mm"
include "grupw.mm"
include "ex.mm"
include "ral2imi.mm"
include "vex.mm"
include "elint2.mm"
include "vpwex.mm"
include "3imtr4g.mm"
include "imp.mm"
include "adantlr.mm"
include "wi.mm"
include "r19.26.mm"
include "grupr.mm"
include "3expia.mm"
include "sylbir.mm"
include "prex.mm"
include "sylan2b.mm"
include "ralrimiv.mm"
include "wf.mm"
include "wb.mm"
include "elmapg.mm"
include "mpan2.mm"
include "ad2antlr.mm"
include "intss1.mm"
include "fss.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "gruurn.mm"
include "syl5.mm"
include "rnex.mm"
include "uniex.mm"
include "syl6ibr.mm"
include "sylbid.mm"
include "3jca.mm"
include "sylanb.mm"
include "elgrug.mm"
include "biimpar.mm"
include "syl12anc.mm"

theorem intgru
  let cA: class A
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A C_ Univ /\ A =/= (/) ) -> |^| A e. Univ )

  proof
    cA
    cgru
    wss
    #
    cA
    c0
    wne
    #
    wa
    #
    cA
    cint
    #
    cvv
    wcel
    #
    @3
    wtr
    #
    vx
    cv
    #
    cpw
    #
    @3
    wcel
    #
    @6
    vy
    cv
    #
    cpr
    #
    @3
    wcel
    #
    vy
    @3
    wral
    #
    @9
    crn
    #
    cuni
    #
    @3
    wcel
    #
    vy
    @3
    @6
    cmap
    co
    #
    wral
    #
    w3a
    #
    vx
    @3
    wral
    #
    @3
    cgru
    wcel
    #
    @2
    @1
    @4
    @0
    @1
    simpr
    cA
    intex
    #
    sylib
    @0
    @5
    @1
    @0
    vu
    cv
    #
    wtr
    #
    vu
    cA
    wral
    #
    @5
    @0
    @22
    cgru
    wcel
    #
    vu
    cA
    wral
    #
    @24
    vu
    cA
    cgru
    dfss3
    #
    @25
    @23
    vu
    cA
    @22
    grutr
    ralimi
    sylbi
    vu
    cA
    trint
    syl
    adantr
    @0
    @26
    @1
    @19
    @27
    @26
    @1
    wa
    #
    @18
    vx
    @3
    @28
    @6
    @3
    wcel
    #
    wa
    #
    @8
    @12
    @17
    @26
    @29
    @8
    @1
    @26
    @29
    @8
    @26
    @6
    @22
    wcel
    #
    vu
    cA
    wral
    #
    @7
    @22
    wcel
    #
    vu
    cA
    wral
    @29
    @8
    @25
    @31
    @33
    vu
    cA
    @25
    @31
    @33
    @6
    @22
    grupw
    ex
    ral2imi
    vu
    @6
    cA
    vx
    vex
    #
    elint2
    #
    vu
    @7
    cA
    vx
    vpwex
    elint2
    3imtr4g
    imp
    adantlr
    @26
    @29
    @12
    @1
    @26
    @29
    wa
    #
    @11
    vy
    @3
    @29
    @26
    @32
    @9
    @3
    wcel
    #
    @11
    wi
    @35
    @26
    @32
    wa
    #
    @9
    @22
    wcel
    #
    vu
    cA
    wral
    #
    @10
    @22
    wcel
    #
    vu
    cA
    wral
    #
    @37
    @11
    @38
    @25
    @31
    wa
    #
    vu
    cA
    wral
    #
    @40
    @42
    wi
    @25
    @31
    vu
    cA
    r19.26
    #
    @43
    @39
    @41
    vu
    cA
    @25
    @31
    @39
    @41
    @6
    @9
    @22
    grupr
    3expia
    ral2imi
    sylbir
    vu
    @9
    cA
    vy
    vex
    #
    elint2
    vu
    @10
    cA
    @6
    @9
    prex
    elint2
    3imtr4g
    sylan2b
    ralrimiv
    adantlr
    @30
    @15
    vy
    @16
    @30
    @9
    @16
    wcel
    #
    @6
    @3
    @9
    wf
    #
    @15
    @1
    @47
    @48
    wb
    #
    @26
    @29
    @1
    @4
    @49
    @21
    @4
    @6
    cvv
    wcel
    @49
    @34
    @3
    @6
    @9
    cvv
    cvv
    elmapg
    mpan2
    sylbi
    ad2antlr
    @26
    @29
    @48
    @15
    wi
    @1
    @36
    @48
    @14
    @22
    wcel
    #
    vu
    cA
    wral
    #
    @15
    @48
    @6
    @22
    @9
    wf
    #
    vu
    cA
    wral
    #
    @36
    @51
    @48
    @52
    vu
    cA
    @22
    cA
    wcel
    @48
    @3
    @22
    wss
    @52
    @22
    cA
    intss1
    @6
    @3
    @22
    @9
    fss
    sylan2
    ralrimiva
    @29
    @26
    @32
    @53
    @51
    wi
    #
    @35
    @38
    @44
    @54
    @45
    @43
    @52
    @50
    vu
    cA
    @25
    @31
    @52
    @50
    @6
    @22
    @9
    gruurn
    3expia
    ral2imi
    sylbir
    sylan2b
    syl5
    vu
    @14
    cA
    @13
    @9
    @46
    rnex
    uniex
    elint2
    syl6ibr
    adantlr
    sylbid
    ralrimiv
    3jca
    ralrimiva
    sylanb
    @4
    @20
    @5
    @19
    wa
    vx
    vy
    @3
    cvv
    elgrug
    biimpar
    syl12anc
end
