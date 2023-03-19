include "cv.mm"
include "cspr.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "cpr.mm"
include "wceq.mm"
include "wrex.mm"
include "copab.mm"
include "wel.mm"
include "prssspr.mm"
include "ad4ant14.mm"
include "wi.mm"
include "wcel.mm"
include "cop.mm"
include "simpr.mm"
include "adantr.mm"
include "eleq1d.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantl.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "adantlr.mm"
include "weq.mm"
include "preq12.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "opelopabga.mm"
include "bicomd.mm"
include "ad3antrrr.mm"
include "mpbid.mm"
include "ex.mm"
include "sylbid.mm"
include "eleq2.mm"
include "ad2antll.mm"
include "cvv.mm"
include "vex.mm"
include "mp2an.mm"
include "eqtr3.mm"
include "equcomd.mm"
include "biimpd.mm"
include "com13.mm"
include "imp.mm"
include "rexlimiva.mm"
include "com12.mm"
include "syl5bi.mm"
include "syld.mm"
include "expimpd.mm"
include "rexlimdva.mm"
include "rexlimiv.mm"
include "mpcom.mm"
include "ssrdv.mm"

theorem sprsymrelf1lem
  let vx: setvar x
  let vy: setvar y
  let cV: class V
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vp: setvar p
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k

  disjoint V c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint x y
  disjoint V p
  disjoint V i
  disjoint V j
  disjoint c p
  disjoint c i
  disjoint c j
  disjoint i p
  disjoint j p
  disjoint i j
  disjoint a i
  disjoint a j
  disjoint a p
  disjoint b i
  disjoint b j
  disjoint b p
  disjoint i x
  disjoint i y
  disjoint j x
  disjoint j y
  disjoint p x
  disjoint p y
  disjoint k x
  assert |- ( ( a C_ ( Pairs ` V ) /\ b C_ ( Pairs ` V ) ) -> ( { <. x , y >. | E. c e. a c = { x , y } } = { <. x , y >. | E. c e. b c = { x , y } } -> a C_ b ) )

  proof
    va
    cv
    #
    cV
    cspr
    cfv
    #
    wss
    #
    vb
    cv
    #
    @1
    wss
    #
    wa
    #
    vc
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    wceq
    #
    vc
    @0
    wrex
    #
    vx
    vy
    copab
    #
    @10
    vc
    @3
    wrex
    #
    vx
    vy
    copab
    #
    wceq
    #
    @0
    @3
    wss
    @5
    @15
    wa
    #
    vp
    @0
    @3
    @16
    vp
    va
    wel
    #
    vp
    vb
    wel
    #
    vp
    cv
    #
    vi
    cv
    #
    vj
    cv
    #
    cpr
    #
    wceq
    #
    vj
    cV
    wrex
    #
    vi
    cV
    wrex
    #
    @16
    @17
    wa
    #
    @18
    @2
    @17
    @25
    @4
    @15
    @0
    cV
    @19
    vi
    vj
    prssspr
    ad4ant14
    @24
    @26
    @18
    wi
    #
    vi
    cV
    @20
    cV
    wcel
    #
    @23
    @27
    vj
    cV
    @28
    @21
    cV
    wcel
    wa
    #
    @23
    @27
    @29
    @23
    wa
    #
    @16
    @17
    @18
    @30
    @16
    wa
    #
    @17
    @20
    @21
    cop
    #
    @12
    wcel
    #
    @18
    @31
    @17
    @22
    @0
    wcel
    #
    @33
    @31
    @19
    @22
    @0
    @30
    @23
    @16
    @29
    @23
    simpr
    adantr
    eleq1d
    @31
    @34
    @33
    @31
    @34
    wa
    @6
    @22
    wceq
    #
    vc
    @0
    wrex
    #
    @33
    @30
    @34
    @36
    @16
    @30
    @34
    wa
    #
    @35
    @22
    @22
    wceq
    #
    vc
    @22
    @0
    @30
    @34
    simpr
    @35
    @35
    @38
    wb
    @37
    @6
    @22
    @22
    eqeq1
    adantl
    @37
    @22
    eqidd
    rspcedvd
    adantlr
    @29
    @36
    @33
    wb
    @23
    @16
    @34
    @29
    @33
    @36
    @11
    @36
    vx
    vy
    @20
    @21
    cV
    cV
    vx
    vi
    weq
    vy
    vj
    weq
    wa
    #
    @10
    @35
    vc
    @0
    @39
    @9
    @22
    @6
    @7
    @8
    @20
    @21
    preq12
    eqeq2d
    #
    rexbidv
    opelopabga
    bicomd
    ad3antrrr
    mpbid
    ex
    sylbid
    @31
    @33
    @32
    @14
    wcel
    #
    @18
    @15
    @33
    @41
    wb
    @30
    @5
    @12
    @14
    @32
    eleq2
    ad2antll
    @41
    @35
    vc
    @3
    wrex
    #
    @31
    @18
    @20
    cvv
    wcel
    @21
    cvv
    wcel
    @41
    @42
    wb
    vi
    vex
    vj
    vex
    @13
    @42
    vx
    vy
    @20
    @21
    cvv
    cvv
    @39
    @10
    @35
    vc
    @3
    @40
    rexbidv
    opelopabga
    mp2an
    @30
    @42
    @18
    wi
    #
    @16
    @23
    @43
    @29
    @42
    @23
    @18
    @35
    @23
    @18
    wi
    #
    vc
    @3
    vc
    vb
    wel
    #
    @35
    @44
    @23
    @35
    @45
    @18
    @23
    @35
    @45
    @18
    wi
    @23
    @35
    wa
    #
    @45
    @18
    @46
    @6
    @19
    @3
    @46
    vp
    vc
    @19
    @6
    @22
    eqtr3
    equcomd
    eleq1d
    biimpd
    ex
    com13
    imp
    rexlimiva
    com12
    adantl
    adantr
    syl5bi
    sylbid
    syld
    expimpd
    ex
    rexlimdva
    rexlimiv
    mpcom
    ex
    ssrdv
    ex
end
