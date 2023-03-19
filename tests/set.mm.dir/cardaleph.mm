include "com.mm"
include "wss.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cale.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "c0.mm"
include "csuc.mm"
include "wrex.mm"
include "wlim.mm"
include "wo.mm"
include "wi.mm"
include "wcel.mm"
include "cardon.mm"
include "eleq1.mm"
include "mpbii.mm"
include "alephle.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "mpdan.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfint.mm"
include "nffv.mm"
include "nfss.mm"
include "onminsb.mm"
include "3syl.mm"
include "a1i.mm"
include "aleph0.mm"
include "syl6eq.mm"
include "sseq1d.mm"
include "biimprd.mm"
include "anim12d.mm"
include "eqss.mm"
include "syl6ibr.mm"
include "com12.mm"
include "ancoms.mm"
include "wn.mm"
include "vex.mm"
include "sucid.mm"
include "eleq2.mm"
include "mpbiri.mm"
include "onnminsb.mm"
include "syl5.mm"
include "imp.mm"
include "adantl.mm"
include "char.mm"
include "alephsuc.mm"
include "sylan9eqr.mm"
include "eleq2d.mm"
include "biimpd.mm"
include "cdom.mm"
include "wbr.mm"
include "elharval.mm"
include "simprbi.mm"
include "cdm.mm"
include "wb.mm"
include "onenon.mm"
include "syl.mm"
include "alephon.mm"
include "ax-mp.mm"
include "carddom2.mm"
include "sylancl.mm"
include "sseq1.mm"
include "alephcard.mm"
include "sseq2i.mm"
include "syl6bb.mm"
include "bitr3d.mm"
include "syl5ib.mm"
include "sylan9r.mm"
include "mtod.mm"
include "rexlimdvaa.mm"
include "onintrab2.mm"
include "sylib.mm"
include "onelon.mm"
include "sylan.mm"
include "adantld.mm"
include "mpcom.mm"
include "onelssi.mm"
include "nsyl.mm"
include "nrexdv.mm"
include "adantr.mm"
include "ciun.mm"
include "alephlim.mm"
include "eliun.mm"
include "mtbird.mm"
include "ex.mm"
include "jaod.mm"
include "onsseleq.mm"
include "mpan2.mm"
include "mpbid.mm"
include "ord.mm"
include "sylsyld.mm"
include "word.mm"
include "eloni.mm"
include "w3o.mm"
include "ordzsl.mm"
include "3orass.mm"
include "bitri.mm"
include "mpjaod.mm"

theorem cardaleph
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( ( _om C_ A /\ ( card ` A ) = A ) -> A = ( aleph ` |^| { x e. On | A C_ ( aleph ` x ) } ) )

  proof
    com
    cA
    wss
    #
    cA
    ccrd
    cfv
    #
    cA
    wceq
    #
    wa
    cA
    vx
    cv
    #
    cale
    cfv
    #
    wss
    #
    vx
    con0
    crab
    #
    cint
    #
    c0
    wceq
    #
    cA
    @7
    cale
    cfv
    #
    wceq
    #
    @7
    vy
    cv
    #
    csuc
    #
    wceq
    #
    vy
    con0
    wrex
    #
    @7
    wlim
    #
    wo
    #
    @2
    @0
    @8
    @10
    wi
    @8
    @2
    @0
    wa
    #
    @10
    @8
    @17
    cA
    @9
    wss
    #
    @9
    cA
    wss
    #
    wa
    @10
    @8
    @2
    @18
    @0
    @19
    @2
    @18
    wi
    @8
    @2
    cA
    con0
    wcel
    #
    @5
    vx
    con0
    wrex
    #
    @18
    @2
    @1
    con0
    wcel
    @20
    cA
    cardon
    @1
    cA
    con0
    eleq1
    mpbii
    #
    @20
    cA
    cA
    cale
    cfv
    #
    wss
    #
    @21
    cA
    alephle
    @5
    @24
    vx
    cA
    con0
    @3
    cA
    wceq
    @4
    @23
    cA
    @3
    cA
    cale
    fveq2
    sseq2d
    rspcev
    mpdan
    #
    @5
    @18
    vx
    vx
    cA
    @9
    vx
    cA
    nfcv
    vx
    @7
    cale
    vx
    cale
    nfcv
    vx
    @6
    @5
    vx
    con0
    nfrab1
    nfint
    nffv
    nfss
    @3
    @7
    wceq
    @4
    @9
    cA
    @3
    @7
    cale
    fveq2
    sseq2d
    onminsb
    #
    3syl
    a1i
    @8
    @19
    @0
    @8
    @9
    com
    cA
    @8
    @9
    c0
    cale
    cfv
    com
    @7
    c0
    cale
    fveq2
    aleph0
    syl6eq
    sseq1d
    biimprd
    anim12d
    cA
    @9
    eqss
    syl6ibr
    com12
    ancoms
    @2
    @16
    @10
    wi
    @0
    @2
    @20
    @16
    cA
    @9
    wcel
    #
    wn
    #
    @10
    @22
    @2
    @14
    @28
    @15
    @2
    @13
    @28
    vy
    con0
    @2
    @11
    con0
    wcel
    #
    @13
    wa
    #
    wa
    @27
    cA
    @11
    cale
    cfv
    #
    wss
    #
    @30
    @32
    wn
    #
    @2
    @29
    @13
    @33
    @13
    @11
    @7
    wcel
    #
    @29
    @33
    @13
    @34
    @11
    @12
    wcel
    @11
    vy
    vex
    sucid
    @7
    @12
    @11
    eleq2
    mpbiri
    @5
    @32
    vx
    @11
    @3
    @11
    wceq
    @4
    @31
    cA
    @3
    @11
    cale
    fveq2
    sseq2d
    onnminsb
    #
    syl5
    imp
    adantl
    @30
    @27
    cA
    @31
    char
    cfv
    #
    wcel
    #
    @2
    @32
    @30
    @27
    @37
    @30
    @9
    @36
    cA
    @13
    @29
    @9
    @12
    cale
    cfv
    @36
    @7
    @12
    cale
    fveq2
    @11
    alephsuc
    sylan9eqr
    eleq2d
    biimpd
    @37
    cA
    @31
    cdom
    wbr
    #
    @2
    @32
    @37
    @20
    @38
    @31
    cA
    elharval
    simprbi
    @2
    @1
    @31
    ccrd
    cfv
    #
    wss
    #
    @38
    @32
    @2
    cA
    ccrd
    cdm
    #
    wcel
    #
    @31
    @41
    wcel
    #
    @40
    @38
    wb
    @2
    @20
    @42
    @22
    cA
    onenon
    syl
    @31
    con0
    wcel
    @43
    @11
    alephon
    #
    @31
    onenon
    ax-mp
    cA
    @31
    carddom2
    sylancl
    @2
    @40
    cA
    @39
    wss
    @32
    @1
    cA
    @39
    sseq1
    @39
    @31
    cA
    @11
    alephcard
    sseq2i
    syl6bb
    bitr3d
    syl5ib
    sylan9r
    mtod
    rexlimdvaa
    @2
    @20
    @15
    @28
    wi
    @22
    @20
    @15
    @28
    @20
    @15
    wa
    #
    @27
    cA
    @31
    wcel
    #
    vy
    @7
    wrex
    #
    @20
    @47
    wn
    @15
    @20
    @46
    vy
    @7
    @20
    @34
    wa
    #
    @32
    @46
    @29
    @48
    @33
    @20
    @7
    con0
    wcel
    #
    @34
    @29
    @20
    @21
    @49
    @25
    @5
    vx
    onintrab2
    sylib
    #
    @7
    @11
    onelon
    sylan
    @29
    @34
    @33
    @20
    @35
    adantld
    mpcom
    @31
    cA
    @44
    onelssi
    nsyl
    nrexdv
    adantr
    @45
    @27
    cA
    vy
    @7
    @31
    ciun
    #
    wcel
    @47
    @45
    @9
    @51
    cA
    @20
    @49
    @15
    @9
    @51
    wceq
    @50
    vy
    @7
    con0
    alephlim
    sylan
    eleq2d
    vy
    cA
    @7
    @31
    eliun
    syl6bb
    mtbird
    ex
    syl
    jaod
    @20
    @27
    @10
    @20
    @18
    @27
    @10
    wo
    #
    @20
    @21
    @18
    @25
    @26
    syl
    @20
    @9
    con0
    wcel
    @18
    @52
    wb
    @7
    alephon
    cA
    @9
    onsseleq
    mpan2
    mpbid
    ord
    sylsyld
    adantl
    @2
    @8
    @16
    wo
    #
    @0
    @2
    @20
    @49
    @53
    @22
    @50
    @49
    @7
    word
    #
    @53
    @7
    eloni
    @54
    @8
    @14
    @15
    w3o
    @53
    vy
    @7
    ordzsl
    @8
    @14
    @15
    3orass
    bitri
    sylib
    3syl
    adantl
    mpjaod
end
