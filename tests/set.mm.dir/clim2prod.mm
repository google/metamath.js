include "cmul.mm"
include "cseq.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cvv.mm"
include "cuz.mm"
include "eqid.mm"
include "cz.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "sseldi.mm"
include "peano2zd.mm"
include "cc.mm"
include "wcel.mm"
include "syl6eleq.mm"
include "eluzel2.mm"
include "syl.mm"
include "prodf.mm"
include "ffvelrnd.mm"
include "seqex.mm"
include "a1i.mm"
include "cv.mm"
include "wss.mm"
include "peano2uz.mm"
include "uzss.mm"
include "3syl.mm"
include "syl6sseqr.mm"
include "sselda.mm"
include "syldan.mm"
include "ffvelrnda.mm"
include "wceq.mm"
include "wi.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "wa.mm"
include "adantr.mm"
include "seqp1.mm"
include "seq1.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "expcom.mm"
include "oveq1.mm"
include "syl6eleqr.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "mpan9.mm"
include "mulassd.mm"
include "3eqtrd.mm"
include "exp31.mm"
include "com12.mm"
include "a2d.mm"
include "uzind4.mm"
include "impcom.mm"
include "climmulc2.mm"

theorem clim2prod
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cZ: class Z
  let vn: setvar n
  let vx: setvar x
  assume clim2prod.1: |- Z = ( ZZ>= ` M )
  assume clim2prod.2: |- ( ph -> N e. Z )
  assume clim2prod.3: |- ( ( ph /\ k e. Z ) -> ( F ` k ) e. CC )
  assume clim2prod.4: |- ( ph -> seq ( N + 1 ) ( x. , F ) ~~> A )

  disjoint A k
  disjoint F k
  disjoint k ph
  disjoint M k
  disjoint N k
  disjoint Z k
  disjoint F n
  disjoint F x
  disjoint k n
  disjoint k x
  disjoint M n
  disjoint M x
  disjoint N n
  disjoint n ph
  disjoint n x
  disjoint N x
  disjoint ph x
  assert |- ( ph -> seq M ( x. , F ) ~~> ( ( seq M ( x. , F ) ` N ) x. A ) )

  proof
    wph
    cA
    cN
    cmul
    cF
    cM
    cseq
    #
    cfv
    #
    vk
    cmul
    cF
    cN
    c1
    caddc
    co
    #
    cseq
    #
    @0
    @2
    cvv
    @2
    cuz
    cfv
    #
    @4
    eqid
    #
    wph
    cN
    wph
    cZ
    cz
    cN
    cZ
    cM
    cuz
    cfv
    #
    cz
    clim2prod.1
    cM
    uzssz
    eqsstri
    clim2prod.2
    sseldi
    peano2zd
    #
    clim2prod.4
    wph
    cZ
    cc
    cN
    @0
    wph
    vk
    cF
    cM
    cZ
    clim2prod.1
    wph
    cN
    @6
    wcel
    #
    cM
    cz
    wcel
    wph
    cN
    cZ
    @6
    clim2prod.2
    clim2prod.1
    syl6eleq
    #
    cM
    cN
    eluzel2
    syl
    clim2prod.3
    prodf
    clim2prod.2
    ffvelrnd
    #
    @0
    cvv
    wcel
    wph
    cmul
    cF
    cM
    seqex
    a1i
    wph
    @4
    cc
    vk
    cv
    #
    @3
    wph
    vk
    cF
    @2
    @4
    @5
    @7
    wph
    @11
    @4
    wcel
    #
    @11
    cZ
    wcel
    @11
    cF
    cfv
    #
    cc
    wcel
    #
    wph
    @4
    cZ
    @11
    wph
    @4
    @6
    cZ
    wph
    @8
    @2
    @6
    wcel
    @4
    @6
    wss
    @9
    cM
    cN
    peano2uz
    cM
    @2
    uzss
    3syl
    #
    clim2prod.1
    syl6sseqr
    sselda
    clim2prod.3
    syldan
    prodf
    #
    ffvelrnda
    @12
    wph
    @11
    @0
    cfv
    #
    @1
    @11
    @3
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wph
    vx
    cv
    #
    @0
    cfv
    #
    @1
    @21
    @3
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    wph
    @2
    @0
    cfv
    #
    @1
    @2
    @3
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    wph
    vn
    cv
    #
    @0
    cfv
    #
    @1
    @30
    @3
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    wph
    @30
    c1
    caddc
    co
    #
    @0
    cfv
    #
    @1
    @35
    @3
    cfv
    #
    cmul
    co
    #
    wceq
    #
    wi
    wph
    @20
    wi
    vx
    vn
    @2
    @11
    @21
    @2
    wceq
    #
    @25
    @29
    wph
    @40
    @22
    @26
    @24
    @28
    @21
    @2
    @0
    fveq2
    @40
    @23
    @27
    @1
    cmul
    @21
    @2
    @3
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    vx
    vn
    weq
    #
    @25
    @34
    wph
    @41
    @22
    @31
    @24
    @33
    @21
    @30
    @0
    fveq2
    @41
    @23
    @32
    @1
    cmul
    @21
    @30
    @3
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    @21
    @35
    wceq
    #
    @25
    @39
    wph
    @42
    @22
    @36
    @24
    @38
    @21
    @35
    @0
    fveq2
    @42
    @23
    @37
    @1
    cmul
    @21
    @35
    @3
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    vx
    vk
    weq
    #
    @25
    @20
    wph
    @43
    @22
    @17
    @24
    @19
    @21
    @11
    @0
    fveq2
    @43
    @23
    @18
    @1
    cmul
    @21
    @11
    @3
    fveq2
    oveq2d
    eqeq12d
    imbi2d
    wph
    @2
    cz
    wcel
    #
    @29
    wph
    @44
    wa
    #
    @26
    @1
    @2
    cF
    cfv
    #
    cmul
    co
    #
    @28
    @45
    @8
    @26
    @47
    wceq
    wph
    @8
    @44
    @9
    adantr
    cmul
    cF
    cM
    cN
    seqp1
    syl
    @45
    @27
    @46
    @1
    cmul
    @44
    @27
    @46
    wceq
    wph
    cmul
    cF
    @2
    seq1
    adantl
    oveq2d
    eqtr4d
    expcom
    @30
    @4
    wcel
    #
    wph
    @34
    @39
    wph
    @48
    @34
    @39
    wi
    wph
    @48
    @34
    @39
    wph
    @48
    wa
    #
    @34
    wa
    #
    @36
    @31
    @35
    cF
    cfv
    #
    cmul
    co
    #
    @33
    @51
    cmul
    co
    #
    @38
    @49
    @36
    @52
    wceq
    #
    @34
    @49
    @30
    @6
    wcel
    #
    @54
    wph
    @4
    @6
    @30
    @15
    sselda
    #
    cmul
    cF
    cM
    @30
    seqp1
    syl
    adantr
    @34
    @52
    @53
    wceq
    @49
    @31
    @33
    @51
    cmul
    oveq1
    adantl
    @50
    @53
    @1
    @32
    @51
    cmul
    co
    #
    cmul
    co
    #
    @38
    @49
    @53
    @58
    wceq
    @34
    @49
    @1
    @32
    @51
    wph
    @1
    cc
    wcel
    @48
    @10
    adantr
    wph
    @4
    cc
    @30
    @3
    @16
    ffvelrnda
    wph
    @48
    @35
    cZ
    wcel
    #
    @51
    cc
    wcel
    #
    @49
    @55
    @59
    @56
    @55
    @35
    @6
    cZ
    cM
    @30
    peano2uz
    clim2prod.1
    syl6eleqr
    syl
    wph
    @14
    vk
    cZ
    wral
    @59
    @60
    wph
    @14
    vk
    cZ
    clim2prod.3
    ralrimiva
    @14
    @60
    vk
    @35
    cZ
    @11
    @35
    wceq
    @13
    @51
    cc
    @11
    @35
    cF
    fveq2
    eleq1d
    rspcv
    mpan9
    syldan
    mulassd
    adantr
    @49
    @38
    @58
    wceq
    @34
    @49
    @37
    @57
    @1
    cmul
    @48
    @37
    @57
    wceq
    wph
    cmul
    cF
    @2
    @30
    seqp1
    adantl
    oveq2d
    adantr
    eqtr4d
    3eqtrd
    exp31
    com12
    a2d
    uzind4
    impcom
    climmulc2
end
