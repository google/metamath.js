include "cr.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "cneg.mm"
include "crab.mm"
include "cmpt.mm"
include "crn.mm"
include "cdm.mm"
include "wral.mm"
include "wceq.mm"
include "ssel.mm"
include "renegcl.mm"
include "syl6.mm"
include "imp.mm"
include "ralrimiva.mm"
include "dmmptg.mm"
include "syl.mm"
include "eqcomd.mm"
include "eleq1d.mm"
include "wfun.mm"
include "wb.mm"
include "funmpt.mm"
include "fundmfibi.mm"
include "mp1i.mm"
include "bitr4d.mm"
include "cvv.mm"
include "wf1.mm"
include "reex.mm"
include "ssex.mm"
include "mptexg.mm"
include "wf1o.mm"
include "eqid.mm"
include "negf1o.mm"
include "f1of1.mm"
include "f1vrnfibi.mm"
include "syl2anc.mm"
include "wrex.mm"
include "cab.mm"
include "wa.mm"
include "adantl.mm"
include "wi.mm"
include "recn.mm"
include "negnegd.mm"
include "biimpcd.mm"
include "jca.mm"
include "mpdan.mm"
include "eleq1.mm"
include "negeq.mm"
include "anbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "simprr.mm"
include "eqeq2d.mm"
include "cc.mm"
include "negneg.mm"
include "ad2antrl.mm"
include "rspcedvd.mm"
include "ex.mm"
include "impbid.mm"
include "abbidv.mm"
include "rnmpt.mm"
include "df-rab.mm"
include "3eqtr4g.mm"
include "3bitrd.mm"
include "biimpa.mm"

theorem negfi
  let cA: class A
  let vn: setvar n
  let va: setvar a
  let vx: setvar x

  disjoint A n
  disjoint A a
  disjoint A x
  disjoint a n
  disjoint a x
  disjoint n x
  assert |- ( ( A C_ RR /\ A e. Fin ) -> { n e. RR | -u n e. A } e. Fin )

  proof
    cA
    cr
    wss
    #
    cA
    cfn
    wcel
    #
    vn
    cv
    #
    cneg
    #
    cA
    wcel
    #
    vn
    cr
    crab
    #
    cfn
    wcel
    #
    @0
    @1
    va
    cA
    va
    cv
    #
    cneg
    #
    cmpt
    #
    cfn
    wcel
    #
    @9
    crn
    #
    cfn
    wcel
    #
    @6
    @0
    @1
    @9
    cdm
    #
    cfn
    wcel
    #
    @10
    @0
    cA
    @13
    cfn
    @0
    @13
    cA
    @0
    @8
    cr
    wcel
    #
    va
    cA
    wral
    @13
    cA
    wceq
    @0
    @15
    va
    cA
    @0
    @7
    cA
    wcel
    #
    @15
    @0
    @16
    @7
    cr
    wcel
    #
    @15
    cA
    cr
    @7
    ssel
    #
    @7
    renegcl
    #
    syl6
    imp
    ralrimiva
    va
    cA
    @8
    cr
    dmmptg
    syl
    eqcomd
    eleq1d
    @9
    wfun
    @10
    @14
    wb
    @0
    va
    cA
    @8
    funmpt
    @9
    fundmfibi
    mp1i
    bitr4d
    @0
    @9
    cvv
    wcel
    #
    cA
    vx
    cv
    cneg
    cA
    wcel
    vx
    cr
    crab
    #
    @9
    wf1
    #
    @10
    @12
    wb
    @0
    cA
    cvv
    wcel
    @20
    cA
    cr
    reex
    ssex
    va
    cA
    @8
    cvv
    mptexg
    syl
    @0
    cA
    @21
    @9
    wf1o
    @22
    va
    cA
    vx
    @9
    @9
    eqid
    #
    negf1o
    cA
    @21
    @9
    f1of1
    syl
    cA
    @21
    @9
    cvv
    f1vrnfibi
    syl2anc
    @0
    @11
    @5
    cfn
    @0
    @2
    @8
    wceq
    #
    va
    cA
    wrex
    #
    vn
    cab
    @2
    cr
    wcel
    #
    @4
    wa
    #
    vn
    cab
    @11
    @5
    @0
    @25
    @27
    vn
    @0
    @25
    @27
    @0
    @24
    @27
    va
    cA
    @0
    @16
    wa
    #
    @27
    @24
    @15
    @8
    cneg
    #
    cA
    wcel
    #
    wa
    #
    @28
    @17
    @31
    @0
    @16
    @17
    @18
    imp
    @28
    @17
    wa
    @15
    @30
    @17
    @15
    @28
    @19
    adantl
    @28
    @17
    @30
    @16
    @17
    @30
    wi
    @0
    @17
    @16
    @30
    @17
    @7
    @29
    cA
    @17
    @29
    @7
    @17
    @7
    @7
    recn
    negnegd
    eqcomd
    eleq1d
    biimpcd
    adantl
    imp
    jca
    mpdan
    @24
    @26
    @15
    @4
    @30
    @2
    @8
    cr
    eleq1
    @24
    @3
    @29
    cA
    @2
    @8
    negeq
    eleq1d
    anbi12d
    syl5ibrcom
    rexlimdva
    @0
    @27
    @25
    @0
    @27
    wa
    #
    @24
    @2
    @3
    cneg
    #
    wceq
    #
    va
    @3
    cA
    @0
    @26
    @4
    simprr
    @7
    @3
    wceq
    #
    @24
    @34
    wb
    @32
    @35
    @8
    @33
    @2
    @7
    @3
    negeq
    eqeq2d
    adantl
    @26
    @34
    @0
    @4
    @26
    @2
    cc
    wcel
    #
    @34
    @2
    recn
    @36
    @33
    @2
    @2
    negneg
    eqcomd
    syl
    ad2antrl
    rspcedvd
    ex
    impbid
    abbidv
    va
    vn
    cA
    @8
    @9
    @23
    rnmpt
    @4
    vn
    cr
    df-rab
    3eqtr4g
    eleq1d
    3bitrd
    biimpa
end
