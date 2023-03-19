include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cmpt.mm"
include "cibl.mm"
include "cmul.mm"
include "co.mm"
include "ccos.mm"
include "citg.mm"
include "cn0.mm"
include "cpi.mm"
include "cdiv.mm"
include "wa.mm"
include "wf.mm"
include "adantr.mm"
include "cneg.mm"
include "cioo.mm"
include "ioossre.mm"
include "id.mm"
include "syl6eleq.mm"
include "sseldi.mm"
include "adantl.mm"
include "ffvelrnd.mm"
include "adantlr.mm"
include "nn0re.mm"
include "remulcld.mm"
include "recoscld.mm"
include "adantll.mm"
include "cof.mm"
include "cvol.mm"
include "cdm.mm"
include "ioombl.mm"
include "eqeltri.mm"
include "a1i.mm"
include "eqidd.mm"
include "offval2.mm"
include "recnd.mm"
include "mulcomd.mm"
include "mpteq2dva.mm"
include "eqtr2d.mm"
include "cmbf.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cc.mm"
include "ccncf.mm"
include "coscn.mm"
include "wss.mm"
include "eqsstri.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "ssid.mm"
include "constcncfg.mm"
include "cncfmptid.mm"
include "mp2an.mm"
include "mulcncf.mm"
include "cncfmpt1f.mm"
include "cnmbf.mm"
include "sylancr.mm"
include "cres.mm"
include "feqmptd.mm"
include "reseq1d.mm"
include "wceq.mm"
include "resmpt.mm"
include "mp1i.mm"
include "eqeltrd.mm"
include "c1.mm"
include "1re.mm"
include "simpr.mm"
include "nfv.mm"
include "nfmpt1.mm"
include "nfdm.mm"
include "nfcri.mm"
include "nfan.mm"
include "wi.mm"
include "ex.mm"
include "ralrimi.mm"
include "dmmptg.mm"
include "syl.mm"
include "eleqtrd.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "fvmptd.mm"
include "abscosbd.mm"
include "eqbrtrd.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "bddmulibl.mm"
include "syl3anc.mm"
include "itgrecl.mm"
include "pire.mm"
include "cc0.mm"
include "wne.mm"
include "0re.mm"
include "pipos.mm"
include "gtneii.mm"
include "redivcld.mm"
include "fmptd.mm"
include "ancli.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "simpl.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "itgeq2dv.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "sylc.mm"
include "jca31.mm"

theorem fourierdlem16
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cC: class C
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vb: setvar b
  let vy: setvar y
  let vk: setvar k
  assume fourierdlem16.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem16.c: |- C = ( -u _pi (,) _pi )
  assume fourierdlem16.fibl: |- ( ph -> ( F |` C ) e. L^1 )
  assume fourierdlem16.a: |- A = ( n e. NN0 |-> ( S. C ( ( F ` x ) x. ( cos ` ( n x. x ) ) ) _d x / _pi ) )
  assume fourierdlem16.n: |- ( ph -> N e. NN0 )

  disjoint C n
  disjoint C x
  disjoint n x
  disjoint F n
  disjoint F x
  disjoint N n
  disjoint N x
  disjoint n ph
  disjoint ph x
  disjoint C b
  disjoint C y
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint n y
  disjoint x y
  disjoint F b
  disjoint F y
  disjoint k x
  assert |- ( ph -> ( ( ( A ` N ) e. RR /\ ( x e. C |-> ( F ` x ) ) e. L^1 ) /\ S. C ( ( F ` x ) x. ( cos ` ( N x. x ) ) ) _d x e. RR ) )

  proof
    wph
    cN
    cA
    cfv
    cr
    wcel
    vx
    cC
    vx
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cibl
    wcel
    #
    vx
    cC
    @1
    cN
    @0
    cmul
    co
    #
    ccos
    cfv
    #
    cmul
    co
    #
    citg
    #
    cr
    wcel
    #
    wph
    cn0
    cr
    cN
    cA
    wph
    vn
    cn0
    vx
    cC
    @1
    vn
    cv
    #
    @0
    cmul
    co
    #
    ccos
    cfv
    #
    cmul
    co
    #
    citg
    #
    cpi
    cdiv
    co
    cr
    cA
    wph
    @9
    cn0
    wcel
    #
    wa
    #
    @13
    cpi
    @15
    vx
    cC
    @12
    @15
    @0
    cC
    wcel
    #
    wa
    #
    @1
    @11
    wph
    @16
    @1
    cr
    wcel
    @14
    wph
    @16
    wa
    cr
    cr
    @0
    cF
    wph
    cr
    cr
    cF
    wf
    @16
    fourierdlem16.f
    adantr
    @16
    @0
    cr
    wcel
    #
    wph
    @16
    cpi
    cneg
    #
    cpi
    cioo
    co
    #
    cr
    @0
    @19
    cpi
    ioossre
    #
    @16
    @0
    cC
    @20
    @16
    id
    fourierdlem16.c
    syl6eleq
    sseldi
    #
    adantl
    ffvelrnd
    adantlr
    #
    @14
    @16
    @11
    cr
    wcel
    #
    wph
    @14
    @16
    wa
    #
    @10
    @25
    @9
    @0
    @14
    @9
    cr
    wcel
    #
    @16
    @9
    nn0re
    #
    adantr
    @16
    @18
    @14
    @22
    adantl
    remulcld
    recoscld
    #
    adantll
    #
    remulcld
    @15
    vx
    cC
    @12
    cmpt
    #
    vx
    cC
    @11
    cmpt
    #
    @2
    cmul
    cof
    co
    #
    cibl
    @15
    @32
    vx
    cC
    @11
    @1
    cmul
    co
    #
    cmpt
    @30
    @15
    vx
    cC
    @11
    @1
    cmul
    @31
    @2
    cvol
    cdm
    #
    cr
    cr
    cC
    @34
    wcel
    #
    @15
    cC
    @20
    @34
    fourierdlem16.c
    @19
    cpi
    ioombl
    eqeltri
    #
    a1i
    @29
    @23
    @15
    @31
    eqidd
    @15
    @2
    eqidd
    offval2
    @15
    vx
    cC
    @33
    @12
    @17
    @11
    @1
    @17
    @11
    @29
    recnd
    @17
    @1
    @23
    recnd
    mulcomd
    mpteq2dva
    eqtr2d
    @15
    @31
    cmbf
    wcel
    #
    @3
    vy
    cv
    #
    @31
    cfv
    #
    cabs
    cfv
    #
    vb
    cv
    #
    cle
    wbr
    #
    vy
    @31
    cdm
    #
    wral
    #
    vb
    cr
    wrex
    #
    @32
    cibl
    wcel
    @14
    @37
    wph
    @14
    @35
    @31
    cC
    cc
    ccncf
    co
    #
    wcel
    @37
    @36
    @14
    vx
    @10
    ccos
    cC
    ccos
    cc
    cc
    ccncf
    co
    wcel
    @14
    coscn
    a1i
    @14
    vx
    @9
    @0
    cC
    @14
    vx
    cC
    @9
    cc
    cC
    cc
    wss
    #
    @14
    cC
    cr
    cc
    cC
    @20
    cr
    fourierdlem16.c
    @21
    eqsstri
    #
    ax-resscn
    sstri
    #
    a1i
    @14
    @9
    @27
    recnd
    cc
    cc
    wss
    #
    @14
    cc
    ssid
    #
    a1i
    constcncfg
    vx
    cC
    @0
    cmpt
    @46
    wcel
    #
    @14
    @47
    @50
    @52
    @49
    @51
    vx
    cC
    cc
    cncfmptid
    mp2an
    a1i
    mulcncf
    cncfmpt1f
    cC
    @31
    cnmbf
    sylancr
    adantl
    wph
    @3
    @14
    wph
    @2
    cF
    cC
    cres
    #
    cibl
    wph
    @53
    vx
    cr
    @1
    cmpt
    #
    cC
    cres
    #
    @2
    wph
    cF
    @54
    cC
    wph
    vx
    cr
    cr
    cF
    fourierdlem16.f
    feqmptd
    reseq1d
    cC
    cr
    wss
    @55
    @2
    wceq
    wph
    @48
    vx
    cr
    cC
    @1
    resmpt
    mp1i
    eqtr2d
    fourierdlem16.fibl
    eqeltrd
    #
    adantr
    @14
    @45
    wph
    @14
    c1
    cr
    wcel
    @40
    c1
    cle
    wbr
    #
    vy
    @43
    wral
    #
    @45
    1re
    @14
    @57
    vy
    @43
    @14
    @38
    @43
    wcel
    #
    @38
    cC
    wcel
    #
    @57
    @14
    @59
    wa
    #
    @38
    @43
    cC
    @14
    @59
    simpr
    @61
    @24
    vx
    cC
    wral
    @43
    cC
    wceq
    @61
    @24
    vx
    cC
    @14
    @59
    vx
    @14
    vx
    nfv
    vx
    vy
    @43
    vx
    @31
    vx
    cC
    @11
    nfmpt1
    nfdm
    nfcri
    nfan
    @14
    @16
    @24
    wi
    @59
    @14
    @16
    @24
    @28
    ex
    adantr
    ralrimi
    vx
    cC
    @11
    cr
    dmmptg
    syl
    eleqtrd
    @14
    @60
    wa
    #
    @40
    @9
    @38
    cmul
    co
    #
    ccos
    cfv
    #
    cabs
    cfv
    #
    c1
    cle
    @62
    @39
    @64
    cabs
    @62
    vx
    @38
    @11
    @64
    cC
    @31
    cr
    @62
    @31
    eqidd
    @0
    @38
    wceq
    #
    @11
    @64
    wceq
    @62
    @66
    @10
    @63
    ccos
    @0
    @38
    @9
    cmul
    oveq2
    fveq2d
    adantl
    @14
    @60
    simpr
    #
    @62
    @63
    @62
    @9
    @38
    @14
    @26
    @60
    @27
    adantr
    @62
    cC
    cr
    @38
    @48
    @67
    sseldi
    remulcld
    #
    recoscld
    fvmptd
    fveq2d
    @62
    @63
    cr
    wcel
    @65
    c1
    cle
    wbr
    @68
    @63
    abscosbd
    syl
    eqbrtrd
    syldan
    ralrimiva
    @44
    @58
    vb
    c1
    cr
    @41
    c1
    wceq
    @42
    @57
    vy
    @43
    @41
    c1
    @40
    cle
    breq2
    ralbidv
    rspcev
    sylancr
    adantl
    vb
    vy
    @31
    @2
    bddmulibl
    syl3anc
    eqeltrd
    itgrecl
    #
    cpi
    cr
    wcel
    @15
    pire
    a1i
    cpi
    cc0
    wne
    @15
    cc0
    cpi
    0re
    pipos
    gtneii
    a1i
    redivcld
    fourierdlem16.a
    fmptd
    fourierdlem16.n
    ffvelrnd
    @56
    wph
    cN
    cn0
    wcel
    #
    wph
    @70
    wa
    #
    @8
    fourierdlem16.n
    wph
    @70
    fourierdlem16.n
    ancli
    @15
    @13
    cr
    wcel
    #
    wi
    @71
    @8
    wi
    vn
    cN
    cn0
    @9
    cN
    wceq
    #
    @15
    @71
    @72
    @8
    @73
    @14
    @70
    wph
    @9
    cN
    cn0
    eleq1
    anbi2d
    @73
    @13
    @7
    cr
    @73
    vx
    cC
    @12
    @6
    @73
    @16
    wa
    #
    @11
    @5
    @1
    cmul
    @74
    @10
    @4
    ccos
    @74
    @9
    cN
    @0
    cmul
    @73
    @16
    simpl
    oveq1d
    fveq2d
    oveq2d
    itgeq2dv
    eleq1d
    imbi12d
    @69
    vtoclg
    sylc
    jca31
end
