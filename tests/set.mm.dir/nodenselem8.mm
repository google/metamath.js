include "csur.mm"
include "wcel.mm"
include "cbday.mm"
include "cfv.mm"
include "wceq.mm"
include "w3a.mm"
include "cslt.mm"
include "wbr.mm"
include "cv.mm"
include "wne.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "c1o.mm"
include "c2o.mm"
include "wa.mm"
include "wi.mm"
include "nodenselem5.mm"
include "exp32.mm"
include "3impia.mm"
include "c0.mm"
include "cop.mm"
include "ctp.mm"
include "wb.mm"
include "sltval2.mm"
include "3adant3.mm"
include "w3o.mm"
include "fvex.mm"
include "brtp.mm"
include "wn.mm"
include "eleq2.mm"
include "biimpd.mm"
include "cpr.mm"
include "nosgnn0.mm"
include "crn.mm"
include "wfn.mm"
include "nofnbday.mm"
include "fnfvelrn.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "sylan.mm"
include "norn.mm"
include "sseld.mm"
include "adantr.mm"
include "syld.mm"
include "mtoi.mm"
include "ex.mm"
include "adantl.mm"
include "syl9r.mm"
include "imp.mm"
include "intnand.mm"
include "3ad2antl1.mm"
include "intnanrd.mm"
include "3orel13.mm"
include "syl2anc.mm"
include "com23.mm"
include "syl5bi.mm"
include "sylbid.mm"
include "mpdd.mm"
include "3mix2.mm"
include "sylibr.mm"
include "syl5ibr.mm"
include "impbid.mm"

theorem nodenselem8
  let cA: class A
  let cB: class B
  let va: setvar a

  disjoint A a
  disjoint B a
  assert |- ( ( A e. No /\ B e. No /\ ( bday ` A ) = ( bday ` B ) ) -> ( A <s B <-> ( ( A ` |^| { a e. On | ( A ` a ) =/= ( B ` a ) } ) = 1o /\ ( B ` |^| { a e. On | ( A ` a ) =/= ( B ` a ) } ) = 2o ) ) )

  proof
    cA
    csur
    wcel
    #
    cB
    csur
    wcel
    #
    cA
    cbday
    cfv
    #
    cB
    cbday
    cfv
    #
    wceq
    #
    w3a
    #
    cA
    cB
    cslt
    wbr
    #
    va
    cv
    #
    cA
    cfv
    @7
    cB
    cfv
    wne
    va
    con0
    crab
    cint
    #
    cA
    cfv
    #
    c1o
    wceq
    #
    @8
    cB
    cfv
    #
    c2o
    wceq
    #
    wa
    #
    @5
    @6
    @8
    @2
    wcel
    #
    @13
    @0
    @1
    @4
    @6
    @14
    wi
    @0
    @1
    wa
    #
    @4
    @6
    @14
    cA
    cB
    va
    nodenselem5
    exp32
    3impia
    @5
    @6
    @9
    @11
    c1o
    c0
    cop
    c1o
    c2o
    cop
    c0
    c2o
    cop
    ctp
    wbr
    #
    @14
    @13
    wi
    #
    @0
    @1
    @6
    @16
    wb
    @4
    cA
    cB
    va
    sltval2
    3adant3
    #
    @16
    @10
    @11
    c0
    wceq
    #
    wa
    #
    @13
    @9
    c0
    wceq
    #
    @12
    wa
    #
    w3o
    #
    @5
    @17
    c1o
    c0
    c1o
    c2o
    c0
    c2o
    @9
    @11
    @8
    cA
    fvex
    @8
    cB
    fvex
    brtp
    #
    @5
    @14
    @23
    @13
    @5
    @14
    @23
    @13
    wi
    #
    @5
    @14
    wa
    #
    @20
    wn
    @22
    wn
    @25
    @26
    @19
    @10
    @5
    @14
    @19
    wn
    #
    @0
    @1
    @4
    @14
    @27
    wi
    @4
    @14
    @8
    @3
    wcel
    #
    @15
    @27
    @4
    @14
    @28
    @2
    @3
    @8
    eleq2
    biimpd
    @1
    @28
    @27
    wi
    @0
    @1
    @28
    @27
    @1
    @28
    wa
    #
    @19
    c0
    c1o
    c2o
    cpr
    #
    wcel
    #
    nosgnn0
    @29
    @19
    c0
    cB
    crn
    #
    wcel
    #
    @31
    @1
    cB
    @3
    wfn
    #
    @28
    @19
    @33
    wi
    cB
    nofnbday
    @34
    @28
    wa
    @11
    @32
    wcel
    @19
    @33
    @3
    @8
    cB
    fnfvelrn
    @11
    c0
    @32
    eleq1
    syl5ibcom
    sylan
    @1
    @33
    @31
    wi
    @28
    @1
    @32
    @30
    c0
    cB
    norn
    sseld
    adantr
    syld
    mtoi
    ex
    adantl
    syl9r
    3impia
    imp
    intnand
    @26
    @21
    @12
    @0
    @1
    @14
    @21
    wn
    @4
    @0
    @14
    wa
    #
    @21
    @31
    nosgnn0
    @35
    @21
    c0
    cA
    crn
    #
    wcel
    #
    @31
    @0
    cA
    @2
    wfn
    #
    @14
    @21
    @37
    wi
    cA
    nofnbday
    @38
    @14
    wa
    @9
    @36
    wcel
    @21
    @37
    @2
    @8
    cA
    fnfvelrn
    @9
    c0
    @36
    eleq1
    syl5ibcom
    sylan
    @0
    @37
    @31
    wi
    @14
    @0
    @36
    @30
    c0
    cA
    norn
    sseld
    adantr
    syld
    mtoi
    3ad2antl1
    intnanrd
    @20
    @13
    @22
    3orel13
    syl2anc
    ex
    com23
    syl5bi
    sylbid
    mpdd
    @13
    @6
    @5
    @16
    @13
    @23
    @16
    @13
    @20
    @22
    3mix2
    @24
    sylibr
    @18
    syl5ibr
    impbid
end
