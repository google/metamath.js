include "csmblfn.mm"
include "cfv.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "clt.mm"
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
include "wceq.mm"
include "restuni4.mm"
include "eqcomd.mm"
include "rabeqd.mm"
include "cvv.mm"
include "uniexd.mm"
include "ssexd.mm"
include "syldan.mm"
include "eqid.mm"
include "subsalsal.mm"
include "cxr.mm"
include "eleqtrd.mm"
include "ffvelrnd.mm"
include "rexrd.mm"
include "adantlr.mm"
include "cle.mm"
include "issmfle.mm"
include "mpbid.mm"
include "simp3d.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "mpbird.mm"
include "rspa.mm"
include "syl2anc.mm"
include "salpreimalegt.mm"
include "eqeltrd.mm"
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
include "simpr3.mm"
include "issmfgtlem.mm"
include "impbid.mm"
include "wb.mm"
include "breq1.mm"
include "rabbidv.mm"
include "fveq2.mm"
include "breq2d.mm"
include "cbvrabv.mm"
include "a1i.mm"
include "eqtrd.mm"
include "cbvralv.mm"
include "3anbi3i.mm"
include "bitrd.mm"

theorem issmfgt
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
  assume issmfgt.s: |- ( ph -> S e. SAlg )
  assume issmfgt.d: |- D = dom F

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
  assert |- ( ph -> ( F e. ( SMblFn ` S ) <-> ( D C_ U. S /\ F : D --> RR /\ A. a e. RR { x e. D | a < ( F ` x ) } e. ( S |`t D ) ) ) )

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
    clt
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
    clt
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
    issmfgt.s
    adantr
    #
    wph
    @0
    simpr
    #
    issmfgt.d
    smfdmss
    #
    @21
    cD
    cS
    cF
    @23
    @24
    issmfgt.d
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
    @4
    cr
    wcel
    #
    @10
    @21
    @28
    wa
    #
    @8
    @7
    vy
    @9
    cuni
    #
    crab
    #
    @9
    @21
    @8
    @31
    wceq
    @28
    @21
    @7
    vy
    cD
    @30
    @21
    @30
    cD
    @21
    cS
    cD
    csalg
    @23
    @25
    restuni4
    #
    eqcomd
    rabeqd
    adantr
    @29
    vy
    @30
    @6
    @4
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
    issmfgt.s
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
    @30
    eqid
    @21
    @5
    @30
    wcel
    #
    @6
    cxr
    wcel
    @28
    @21
    @34
    wa
    #
    @6
    @35
    cD
    cr
    @5
    cF
    @21
    @3
    @34
    @26
    adantr
    @35
    @5
    @30
    cD
    @21
    @34
    simpr
    @21
    @30
    cD
    wceq
    @34
    @32
    adantr
    eleqtrd
    ffvelrnd
    rexrd
    adantlr
    @21
    vc
    cv
    #
    cr
    wcel
    #
    @6
    @36
    cle
    wbr
    #
    vy
    @30
    crab
    #
    @9
    wcel
    #
    @28
    @21
    @37
    wa
    @40
    vc
    cr
    wral
    #
    @37
    @40
    @21
    @41
    @37
    @21
    @41
    @38
    vy
    cD
    crab
    #
    @9
    wcel
    #
    vc
    cr
    wral
    #
    @21
    @2
    @3
    @44
    @21
    @0
    @2
    @3
    @44
    w3a
    @24
    @21
    vy
    cD
    cS
    cF
    vc
    @23
    issmfgt.d
    issmfle
    mpbid
    simp3d
    @21
    @40
    @43
    vc
    cr
    @21
    @39
    @42
    @9
    @21
    @38
    vy
    @30
    cD
    @32
    rabeqd
    eleq1d
    ralbidv
    mpbird
    adantr
    @21
    @37
    simpr
    @40
    vc
    cr
    rspa
    syl2anc
    adantlr
    @21
    @28
    simpr
    salpreimalegt
    eqeltrd
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
    @33
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
    issmfgt.s
    adantr
    issmfgt.d
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
    issmfgtlem
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
    @45
    @8
    @13
    @6
    clt
    wbr
    #
    vy
    cD
    crab
    #
    @17
    @45
    @7
    @46
    vy
    cD
    @4
    @13
    @6
    clt
    breq1
    rabbidv
    @47
    @17
    wceq
    @45
    @46
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
    clt
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
