include "csmblfn.mm"
include "cfv.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "crest.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "wa.mm"
include "csalg.mm"
include "adantr.mm"
include "simpr.mm"
include "smfdmss.mm"
include "smff.mm"
include "nfv.mm"
include "nfan.mm"
include "cvv.mm"
include "uniexd.mm"
include "ssexd.mm"
include "syldan.mm"
include "eqid.mm"
include "subsalsal.mm"
include "cxr.mm"
include "frexr.mm"
include "ffvelrnda.mm"
include "clt.mm"
include "smfpreimalt.mm"
include "adantlr.mm"
include "salpreimaltle.mm"
include "ex.mm"
include "ralrimi.mm"
include "3jca.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfel.mm"
include "nfral.mm"
include "nf3an.mm"
include "nfra1.mm"
include "simpr1.mm"
include "simpr2.mm"
include "rspa.mm"
include "3ad2antl3.mm"
include "adantll.mm"
include "issmflelem.mm"
include "impbid.mm"
include "wb.mm"
include "wceq.mm"
include "breq2.mm"
include "rabbidv.mm"
include "fveq2.mm"
include "breq1d.mm"
include "cbvrabv.mm"
include "a1i.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "3anbi3i.mm"
include "bitrd.mm"

theorem issmfle
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cS: class S
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vy: setvar y
  let vc: setvar c
  let vk: setvar k
  assume issmfle.s: |- ( ph -> S e. SAlg )
  assume issmfle.d: |- D = dom F

  disjoint D a
  disjoint D x
  disjoint a x
  disjoint F a
  disjoint F x
  disjoint S a
  disjoint D b
  disjoint D y
  disjoint a b
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint D c
  disjoint b c
  disjoint c y
  disjoint F b
  disjoint F y
  disjoint F c
  disjoint S b
  disjoint S y
  disjoint S c
  disjoint b ph
  disjoint c ph
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( F e. ( SMblFn ` S ) <-> ( D C_ U. S /\ F : D --> RR /\ A. a e. RR { x e. D | ( F ` x ) <_ a } e. ( S |`t D ) ) ) )

  proof
    wph
    cF
    cS
    csmblfn
    cfv
    wcel
    #
    cD
    cS
    cuni
    #
    wss
    #
    cD
    cr
    cF
    wf
    #
    vy
    cv
    #
    cF
    cfv
    #
    vb
    cv
    #
    cle
    wbr
    #
    vy
    cD
    crab
    #
    cS
    cD
    crest
    co
    #
    wcel
    #
    vb
    cr
    wral
    #
    w3a
    #
    @2
    @3
    vx
    cv
    #
    cF
    cfv
    #
    va
    cv
    #
    cle
    wbr
    #
    vx
    cD
    crab
    #
    @9
    wcel
    #
    va
    cr
    wral
    #
    w3a
    #
    wph
    @0
    @12
    wph
    @0
    @12
    wph
    @0
    wa
    #
    @2
    @3
    @11
    @21
    cD
    cS
    cF
    wph
    cS
    csalg
    wcel
    #
    @0
    issmfle.s
    adantr
    #
    wph
    @0
    simpr
    #
    issmfle.d
    smfdmss
    #
    @21
    cD
    cS
    cF
    @23
    @24
    issmfle.d
    smff
    #
    @21
    @10
    vb
    cr
    wph
    @0
    vb
    wph
    vb
    nfv
    #
    @0
    vb
    nfv
    nfan
    @21
    @6
    cr
    wcel
    #
    @10
    @21
    @28
    wa
    #
    vy
    cD
    @5
    @6
    @9
    vc
    @21
    @28
    vy
    wph
    @0
    vy
    wph
    vy
    nfv
    #
    @0
    vy
    nfv
    nfan
    @28
    vy
    nfv
    nfan
    @29
    vc
    nfv
    @21
    @9
    csalg
    wcel
    @28
    @21
    cD
    cS
    @9
    cvv
    @23
    wph
    @0
    @2
    cD
    cvv
    wcel
    @25
    wph
    @2
    wa
    cD
    @1
    cvv
    wph
    @1
    cvv
    wcel
    @2
    wph
    cS
    csalg
    issmfle.s
    uniexd
    adantr
    wph
    @2
    simpr
    ssexd
    syldan
    @9
    eqid
    subsalsal
    adantr
    @29
    cD
    cxr
    @4
    cF
    @21
    cD
    cxr
    cF
    wf
    @28
    @21
    cD
    cF
    @26
    frexr
    adantr
    ffvelrnda
    @21
    vc
    cv
    #
    cr
    wcel
    #
    @5
    @31
    clt
    wbr
    vy
    cD
    crab
    @9
    wcel
    @28
    @21
    @32
    wa
    vy
    @31
    cD
    cS
    cF
    @21
    @22
    @32
    @23
    adantr
    @21
    @0
    @32
    @24
    adantr
    issmfle.d
    @21
    @32
    simpr
    smfpreimalt
    adantlr
    @21
    @28
    simpr
    salpreimaltle
    ex
    ralrimi
    3jca
    ex
    wph
    @12
    @0
    wph
    @12
    wa
    vy
    cD
    cS
    cF
    vb
    wph
    @12
    vy
    @30
    @2
    @3
    @11
    vy
    @2
    vy
    nfv
    @3
    vy
    nfv
    @10
    vy
    vb
    cr
    vy
    cr
    nfcv
    vy
    @8
    @9
    @7
    vy
    cD
    nfrab1
    vy
    @9
    nfcv
    nfel
    nfral
    nf3an
    nfan
    wph
    @12
    vb
    @27
    @2
    @3
    @11
    vb
    @2
    vb
    nfv
    @3
    vb
    nfv
    @10
    vb
    cr
    nfra1
    nf3an
    nfan
    wph
    @22
    @12
    issmfle.s
    adantr
    issmfle.d
    wph
    @2
    @3
    @11
    simpr1
    wph
    @2
    @3
    @11
    simpr2
    @12
    @28
    @10
    wph
    @11
    @2
    @28
    @10
    @3
    @10
    vb
    cr
    rspa
    3ad2antl3
    adantll
    issmflelem
    ex
    impbid
    @12
    @20
    wb
    wph
    @11
    @19
    @2
    @3
    @10
    @18
    vb
    va
    cr
    @6
    @15
    wceq
    #
    @8
    @17
    @9
    @33
    @8
    @5
    @15
    cle
    wbr
    #
    vy
    cD
    crab
    #
    @17
    @33
    @7
    @34
    vy
    cD
    @6
    @15
    @5
    cle
    breq2
    rabbidv
    @35
    @17
    wceq
    @33
    @34
    @16
    vy
    vx
    cD
    @4
    @13
    wceq
    @5
    @14
    @15
    cle
    @4
    @13
    cF
    fveq2
    breq1d
    cbvrabv
    a1i
    eqtrd
    eleq1d
    cbvralv
    3anbi3i
    a1i
    bitrd
end
