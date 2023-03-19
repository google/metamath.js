include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "wcel.mm"
include "crpss.mm"
include "wor.mm"
include "cuni.mm"
include "wi.mm"
include "cv.mm"
include "wtru.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "eqneqall.mm"
include "tru.mm"
include "a1i.mm"
include "2thd.mm"
include "neeq1.mm"
include "soeq2.mm"
include "unieq.mm"
include "id.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "w3a.mm"
include "vex.mm"
include "unisn.mm"
include "vsnid.mm"
include "eqeltri.mm"
include "uneq1.mm"
include "uncom.mm"
include "un0.mm"
include "eqtri.mm"
include "syl6eq.mm"
include "unieqd.mm"
include "mpbiri.mm"
include "a1d.mm"
include "adantl.mm"
include "wa.mm"
include "simpr.mm"
include "wss.mm"
include "ssun1.mm"
include "simpl2.mm"
include "soss.mm"
include "mpsyl.mm"
include "uniun.mm"
include "uneq2i.mm"
include "wo.mm"
include "simprr.mm"
include "elun1.mm"
include "ad2antll.mm"
include "ssun2.mm"
include "sselii.mm"
include "sorpssi.mm"
include "syl12anc.mm"
include "ssequn1.mm"
include "eleq1.mm"
include "syl5ibr.mm"
include "sylbi.mm"
include "impcom.mm"
include "syl5eqel.mm"
include "jaodan.mm"
include "syl2anc.mm"
include "expr.mm"
include "embantd.mm"
include "pm2.61dane.mm"
include "3exp.mm"
include "com24.mm"
include "findcard2.mm"
include "com12.mm"
include "3imp.mm"

theorem fin1a2lem10
  let cA: class A
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V
  let cX: class X
  let cC: class C


  assert |- ( ( A =/= (/) /\ A e. Fin /\ [C.] Or A ) -> U. A e. A )

  proof
    cA
    c0
    wne
    #
    cA
    cfn
    wcel
    #
    cA
    crpss
    wor
    #
    cA
    cuni
    #
    cA
    wcel
    #
    @1
    @0
    @2
    @4
    wi
    #
    va
    cv
    #
    c0
    wne
    #
    @6
    crpss
    wor
    #
    @6
    cuni
    #
    @6
    wcel
    #
    wi
    #
    wi
    #
    wtru
    vb
    cv
    #
    c0
    wne
    #
    @13
    crpss
    wor
    #
    @13
    cuni
    #
    @13
    wcel
    #
    wi
    #
    wi
    #
    @13
    vc
    cv
    #
    csn
    #
    cun
    #
    c0
    wne
    #
    @22
    crpss
    wor
    #
    @22
    cuni
    #
    @22
    wcel
    #
    wi
    #
    wi
    @0
    @5
    wi
    va
    vb
    vc
    cA
    @6
    c0
    wceq
    #
    @12
    wtru
    @11
    @6
    c0
    eqneqall
    wtru
    @28
    tru
    a1i
    2thd
    @6
    @13
    wceq
    #
    @7
    @14
    @11
    @18
    @6
    @13
    c0
    neeq1
    @29
    @8
    @15
    @10
    @17
    @6
    @13
    crpss
    soeq2
    @29
    @9
    @16
    @6
    @13
    @6
    @13
    unieq
    @29
    id
    eleq12d
    imbi12d
    imbi12d
    @6
    @22
    wceq
    #
    @7
    @23
    @11
    @27
    @6
    @22
    c0
    neeq1
    @30
    @8
    @24
    @10
    @26
    @6
    @22
    crpss
    soeq2
    @30
    @9
    @25
    @6
    @22
    @6
    @22
    unieq
    @30
    id
    eleq12d
    imbi12d
    imbi12d
    @6
    cA
    wceq
    #
    @7
    @0
    @11
    @5
    @6
    cA
    c0
    neeq1
    @31
    @8
    @2
    @10
    @4
    @6
    cA
    crpss
    soeq2
    @31
    @9
    @3
    @6
    cA
    @6
    cA
    unieq
    @31
    id
    eleq12d
    imbi12d
    imbi12d
    tru
    @13
    cfn
    wcel
    #
    @24
    @23
    @19
    @26
    @32
    @24
    @23
    @19
    @26
    wi
    #
    @32
    @24
    @23
    w3a
    #
    @33
    @13
    c0
    @13
    c0
    wceq
    #
    @33
    @34
    @35
    @26
    @19
    @35
    @26
    @21
    cuni
    #
    @21
    wcel
    @36
    @20
    @21
    @20
    vc
    vex
    unisn
    #
    vc
    vsnid
    #
    eqeltri
    @35
    @25
    @36
    @22
    @21
    @35
    @22
    @21
    @35
    @22
    c0
    @21
    cun
    #
    @21
    @13
    c0
    @21
    uneq1
    @39
    @21
    c0
    cun
    @21
    c0
    @21
    uncom
    @21
    un0
    eqtri
    syl6eq
    #
    unieqd
    @40
    eleq12d
    mpbiri
    a1d
    adantl
    @34
    @14
    wa
    #
    @14
    @18
    @26
    @34
    @14
    simpr
    @41
    @15
    @17
    @26
    @13
    @22
    wss
    @41
    @24
    @15
    @13
    @21
    ssun1
    @32
    @24
    @23
    @14
    simpl2
    @13
    @22
    crpss
    soss
    mpsyl
    @34
    @14
    @17
    @26
    @34
    @14
    @17
    wa
    #
    wa
    #
    @25
    @16
    @20
    cun
    #
    @22
    @25
    @16
    @36
    cun
    @44
    @13
    @21
    uniun
    @36
    @20
    @16
    @37
    uneq2i
    eqtri
    @43
    @17
    @16
    @20
    wss
    #
    @20
    @16
    wss
    #
    wo
    #
    @44
    @22
    wcel
    #
    @34
    @14
    @17
    simprr
    @43
    @24
    @16
    @22
    wcel
    #
    @20
    @22
    wcel
    #
    @47
    @32
    @24
    @23
    @42
    simpl2
    @17
    @49
    @34
    @14
    @16
    @13
    @21
    elun1
    #
    ad2antll
    @50
    @43
    @21
    @22
    @20
    @21
    @13
    ssun2
    @38
    sselii
    #
    a1i
    @22
    @16
    @20
    sorpssi
    syl12anc
    @17
    @45
    @48
    @46
    @45
    @17
    @48
    @45
    @44
    @20
    wceq
    #
    @17
    @48
    wi
    @16
    @20
    ssequn1
    @17
    @48
    @53
    @50
    @50
    @17
    @52
    a1i
    @44
    @20
    @22
    eleq1
    syl5ibr
    sylbi
    impcom
    @17
    @46
    wa
    @44
    @20
    @16
    cun
    #
    @22
    @16
    @20
    uncom
    @46
    @17
    @54
    @22
    wcel
    #
    @46
    @54
    @16
    wceq
    #
    @17
    @55
    wi
    @20
    @16
    ssequn1
    @17
    @55
    @56
    @49
    @51
    @54
    @16
    @22
    eleq1
    syl5ibr
    sylbi
    impcom
    syl5eqel
    jaodan
    syl2anc
    syl5eqel
    expr
    embantd
    embantd
    pm2.61dane
    3exp
    com24
    findcard2
    com12
    3imp
end
