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
include "ffvelrnda.mm"
include "rexrd.mm"
include "adantlr.mm"
include "clt.mm"
include "smfpreimagt.mm"
include "salpreimagtge.mm"
include "ralrimiva.mm"
include "3jca.mm"
include "ex.mm"
include "nfcv.mm"
include "nfrab1.mm"
include "nfel.mm"
include "nfral.mm"
include "nf3an.mm"
include "nfra1.mm"
include "simpr1.mm"
include "simpr2.mm"
include "simpr3.mm"
include "issmfgelem.mm"
include "impbid.mm"
include "wb.mm"
include "wceq.mm"
include "breq1.mm"
include "rabbidv.mm"
include "fveq2.mm"
include "breq2d.mm"
include "cbvrabv.mm"
include "a1i.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "cbvralv.mm"
include "3anbi3i.mm"
include "bitrd.mm"

theorem issmfge
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
  assume issmfge.s: |- ( ph -> S e. SAlg )
  assume issmfge.d: |- D = dom F

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
  assert |- ( ph -> ( F e. ( SMblFn ` S ) <-> ( D C_ U. S /\ F : D --> RR /\ A. a e. RR { x e. D | a <_ ( F ` x ) } e. ( S |`t D ) ) ) )

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
    vb
    cv
    #
    vy
    cv
    #
    cF
    cfv
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
    va
    cv
    #
    vx
    cv
    #
    cF
    cfv
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
    issmfge.s
    adantr
    #
    wph
    @0
    simpr
    #
    issmfge.d
    smfdmss
    #
    @21
    cD
    cS
    cF
    @23
    @24
    issmfge.d
    smff
    #
    @21
    @10
    vb
    cr
    @21
    @4
    cr
    wcel
    #
    wa
    #
    vy
    cD
    @6
    @4
    @9
    vc
    @21
    @27
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
    @27
    vy
    nfv
    nfan
    @28
    vc
    nfv
    @21
    @9
    csalg
    wcel
    @27
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
    issmfge.s
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
    @21
    @5
    cD
    wcel
    #
    @6
    cxr
    wcel
    @27
    @21
    @30
    wa
    @6
    @21
    cD
    cr
    @5
    cF
    @26
    ffvelrnda
    rexrd
    adantlr
    @21
    vc
    cv
    #
    cr
    wcel
    #
    @31
    @6
    clt
    wbr
    vy
    cD
    crab
    @9
    wcel
    @27
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
    issmfge.d
    @21
    @32
    simpr
    smfpreimagt
    adantlr
    @21
    @27
    simpr
    salpreimagtge
    ralrimiva
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
    @29
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
    wph
    vb
    nfv
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
    issmfge.s
    adantr
    issmfge.d
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
    wph
    @2
    @3
    @11
    simpr3
    issmfgelem
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
    @4
    @13
    wceq
    #
    @8
    @17
    @9
    @33
    @8
    @13
    @6
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
    @4
    @13
    @6
    cle
    breq1
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
    @5
    @14
    wceq
    @6
    @15
    @13
    cle
    @5
    @14
    cF
    fveq2
    breq2d
    cbvrabv
    a1i
    eqtrd
    eleq1d
    cbvralv
    3anbi3i
    a1i
    bitrd
end
