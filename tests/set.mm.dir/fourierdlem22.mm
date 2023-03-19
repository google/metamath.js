include "cv.mm"
include "cn0.mm"
include "wcel.mm"
include "cfv.mm"
include "cr.mm"
include "wi.mm"
include "cn.mm"
include "cmul.mm"
include "co.mm"
include "ccos.mm"
include "citg.mm"
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
include "cmpt.mm"
include "cof.mm"
include "cibl.mm"
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
include "ffvelrnda.mm"
include "csin.mm"
include "nnnn0.mm"
include "resincld.mm"
include "sincn.mm"
include "abssinbd.mm"
include "sylan2.mm"
include "jca.mm"

theorem fourierdlem22
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vn: setvar n
  let cF: class F
  let vb: setvar b
  let vy: setvar y
  let vk: setvar k
  assume fourierdlem22.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem22.c: |- C = ( -u _pi (,) _pi )
  assume fourierdlem22.fibl: |- ( ph -> ( F |` C ) e. L^1 )
  assume fourierdlem22.a: |- A = ( n e. NN0 |-> ( S. C ( ( F ` x ) x. ( cos ` ( n x. x ) ) ) _d x / _pi ) )
  assume fourierdlem22.b: |- B = ( n e. NN |-> ( S. C ( ( F ` x ) x. ( sin ` ( n x. x ) ) ) _d x / _pi ) )

  disjoint C x
  disjoint F x
  disjoint n x
  disjoint n ph
  disjoint ph x
  disjoint C b
  disjoint C y
  disjoint b x
  disjoint b y
  disjoint x y
  disjoint F b
  disjoint F y
  disjoint b n
  disjoint n y
  disjoint k x
  assert |- ( ph -> ( ( n e. NN0 -> ( A ` n ) e. RR ) /\ ( n e. NN -> ( B ` n ) e. RR ) ) )

  proof
    wph
    vn
    cv
    #
    cn0
    wcel
    #
    @0
    cA
    cfv
    cr
    wcel
    #
    wi
    @0
    cn
    wcel
    #
    @0
    cB
    cfv
    cr
    wcel
    #
    wi
    wph
    @1
    @2
    wph
    cn0
    cr
    @0
    cA
    wph
    vn
    cn0
    vx
    cC
    vx
    cv
    #
    cF
    cfv
    #
    @0
    @5
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
    @1
    wa
    #
    @10
    cpi
    @11
    vx
    cC
    @9
    @11
    @5
    cC
    wcel
    #
    wa
    #
    @6
    @8
    wph
    @12
    @6
    cr
    wcel
    @1
    wph
    @12
    wa
    cr
    cr
    @5
    cF
    wph
    cr
    cr
    cF
    wf
    @12
    fourierdlem22.f
    adantr
    @12
    @5
    cr
    wcel
    #
    wph
    @12
    cpi
    cneg
    #
    cpi
    cioo
    co
    #
    cr
    @5
    @15
    cpi
    ioossre
    #
    @12
    @5
    cC
    @16
    @12
    id
    fourierdlem22.c
    syl6eleq
    sseldi
    #
    adantl
    ffvelrnd
    adantlr
    #
    @1
    @12
    @8
    cr
    wcel
    #
    wph
    @1
    @12
    wa
    #
    @7
    @21
    @0
    @5
    @1
    @0
    cr
    wcel
    #
    @12
    @0
    nn0re
    #
    adantr
    @12
    @14
    @1
    @18
    adantl
    remulcld
    #
    recoscld
    #
    adantll
    #
    remulcld
    @11
    vx
    cC
    @9
    cmpt
    #
    vx
    cC
    @8
    cmpt
    #
    vx
    cC
    @6
    cmpt
    #
    cmul
    cof
    #
    co
    #
    cibl
    @11
    @31
    vx
    cC
    @8
    @6
    cmul
    co
    #
    cmpt
    @27
    @11
    vx
    cC
    @8
    @6
    cmul
    @28
    @29
    cvol
    cdm
    #
    cr
    cr
    cC
    @33
    wcel
    #
    @11
    cC
    @16
    @33
    fourierdlem22.c
    @15
    cpi
    ioombl
    eqeltri
    #
    a1i
    #
    @26
    @19
    @11
    @28
    eqidd
    @11
    @29
    eqidd
    #
    offval2
    @11
    vx
    cC
    @32
    @9
    @13
    @8
    @6
    @13
    @8
    @26
    recnd
    @13
    @6
    @19
    recnd
    #
    mulcomd
    mpteq2dva
    eqtr2d
    @11
    @28
    cmbf
    wcel
    #
    @29
    cibl
    wcel
    #
    vy
    cv
    #
    @28
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
    @28
    cdm
    #
    wral
    #
    vb
    cr
    wrex
    #
    @31
    cibl
    wcel
    @1
    @39
    wph
    @1
    @34
    @28
    cC
    cc
    ccncf
    co
    #
    wcel
    @39
    @35
    @1
    vx
    @7
    ccos
    cC
    ccos
    cc
    cc
    ccncf
    co
    #
    wcel
    @1
    coscn
    a1i
    @1
    vx
    @0
    @5
    cC
    @1
    vx
    cC
    @0
    cc
    cC
    cc
    wss
    #
    @1
    cC
    cr
    cc
    cC
    @16
    cr
    fourierdlem22.c
    @17
    eqsstri
    #
    ax-resscn
    sstri
    #
    a1i
    @1
    @0
    @23
    recnd
    cc
    cc
    wss
    #
    @1
    cc
    ssid
    #
    a1i
    constcncfg
    vx
    cC
    @5
    cmpt
    @49
    wcel
    #
    @1
    @51
    @54
    @56
    @53
    @55
    vx
    cC
    cc
    cncfmptid
    mp2an
    a1i
    mulcncf
    #
    cncfmpt1f
    cC
    @28
    cnmbf
    sylancr
    adantl
    wph
    @40
    @1
    wph
    @29
    cF
    cC
    cres
    #
    cibl
    wph
    @58
    vx
    cr
    @6
    cmpt
    #
    cC
    cres
    #
    @29
    wph
    cF
    @59
    cC
    wph
    vx
    cr
    cr
    cF
    fourierdlem22.f
    feqmptd
    reseq1d
    cC
    cr
    wss
    @60
    @29
    wceq
    wph
    @52
    vx
    cr
    cC
    @6
    resmpt
    mp1i
    eqtr2d
    fourierdlem22.fibl
    eqeltrd
    adantr
    #
    @1
    @48
    wph
    @1
    c1
    cr
    wcel
    #
    @43
    c1
    cle
    wbr
    #
    vy
    @46
    wral
    #
    @48
    1re
    @1
    @63
    vy
    @46
    @1
    @41
    @46
    wcel
    #
    @41
    cC
    wcel
    #
    @63
    @1
    @65
    wa
    #
    @41
    @46
    cC
    @1
    @65
    simpr
    @67
    @20
    vx
    cC
    wral
    @46
    cC
    wceq
    @67
    @20
    vx
    cC
    @1
    @65
    vx
    @1
    vx
    nfv
    #
    vx
    vy
    @46
    vx
    @28
    vx
    cC
    @8
    nfmpt1
    nfdm
    nfcri
    nfan
    @1
    @12
    @20
    wi
    @65
    @1
    @12
    @20
    @25
    ex
    adantr
    ralrimi
    vx
    cC
    @8
    cr
    dmmptg
    syl
    eleqtrd
    @1
    @66
    wa
    #
    @43
    @0
    @41
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
    @69
    @42
    @71
    cabs
    @69
    vx
    @41
    @8
    @71
    cC
    @28
    cr
    @69
    @28
    eqidd
    @5
    @41
    wceq
    #
    @8
    @71
    wceq
    @69
    @73
    @7
    @70
    ccos
    @5
    @41
    @0
    cmul
    oveq2
    #
    fveq2d
    adantl
    @1
    @66
    simpr
    #
    @69
    @70
    @69
    @0
    @41
    @1
    @22
    @66
    @23
    adantr
    @69
    cC
    cr
    @41
    @52
    @75
    sseldi
    remulcld
    #
    recoscld
    fvmptd
    fveq2d
    @69
    @70
    cr
    wcel
    #
    @72
    c1
    cle
    wbr
    @76
    @70
    abscosbd
    syl
    eqbrtrd
    syldan
    ralrimiva
    @47
    @64
    vb
    c1
    cr
    @44
    c1
    wceq
    #
    @45
    @63
    vy
    @46
    @44
    c1
    @43
    cle
    breq2
    ralbidv
    rspcev
    sylancr
    adantl
    vb
    vy
    @28
    @29
    bddmulibl
    syl3anc
    eqeltrd
    itgrecl
    cpi
    cr
    wcel
    #
    @11
    pire
    a1i
    cpi
    cc0
    wne
    #
    @11
    cc0
    cpi
    0re
    pipos
    gtneii
    #
    a1i
    redivcld
    fourierdlem22.a
    fmptd
    ffvelrnda
    ex
    wph
    @3
    @4
    wph
    cn
    cr
    @0
    cB
    wph
    vn
    cn
    vx
    cC
    @6
    @7
    csin
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
    cB
    wph
    @3
    wa
    #
    @84
    cpi
    @3
    wph
    @1
    @84
    cr
    wcel
    @0
    nnnn0
    @11
    vx
    cC
    @83
    @13
    @6
    @82
    @19
    @1
    @12
    @82
    cr
    wcel
    #
    wph
    @21
    @7
    @24
    resincld
    #
    adantll
    #
    remulcld
    @11
    vx
    cC
    @83
    cmpt
    #
    vx
    cC
    @82
    cmpt
    #
    @29
    @30
    co
    #
    cibl
    @11
    @91
    vx
    cC
    @82
    @6
    cmul
    co
    #
    cmpt
    @89
    @11
    vx
    cC
    @82
    @6
    cmul
    @90
    @29
    @33
    cr
    cr
    @36
    @88
    @19
    @11
    @90
    eqidd
    @37
    offval2
    @11
    vx
    cC
    @92
    @83
    @13
    @82
    @6
    @13
    @82
    @88
    recnd
    @38
    mulcomd
    mpteq2dva
    eqtr2d
    @11
    @90
    cmbf
    wcel
    #
    @40
    @41
    @90
    cfv
    #
    cabs
    cfv
    #
    @44
    cle
    wbr
    #
    vy
    @90
    cdm
    #
    wral
    #
    vb
    cr
    wrex
    #
    @91
    cibl
    wcel
    @11
    @34
    @90
    @49
    wcel
    @93
    @35
    @11
    vx
    @7
    csin
    cC
    csin
    @50
    wcel
    @11
    sincn
    a1i
    @1
    vx
    cC
    @7
    cmpt
    @49
    wcel
    wph
    @57
    adantl
    cncfmpt1f
    cC
    @90
    cnmbf
    sylancr
    @61
    @1
    @99
    wph
    @1
    @62
    @95
    c1
    cle
    wbr
    #
    vy
    @97
    wral
    #
    @99
    1re
    @1
    @100
    vy
    @97
    @1
    @41
    @97
    wcel
    #
    @66
    @100
    @1
    @102
    wa
    #
    @41
    @97
    cC
    @1
    @102
    simpr
    @103
    @86
    vx
    cC
    wral
    @97
    cC
    wceq
    @103
    @86
    vx
    cC
    @1
    @102
    vx
    @68
    vx
    vy
    @97
    vx
    @90
    vx
    cC
    @82
    nfmpt1
    nfdm
    nfcri
    nfan
    @1
    @12
    @86
    wi
    @102
    @1
    @12
    @86
    @87
    ex
    adantr
    ralrimi
    vx
    cC
    @82
    cr
    dmmptg
    syl
    eleqtrd
    @69
    @95
    @70
    csin
    cfv
    #
    cabs
    cfv
    #
    c1
    cle
    @69
    @94
    @104
    cabs
    @69
    vx
    @41
    @82
    @104
    cC
    @90
    cr
    @69
    @90
    eqidd
    @73
    @82
    @104
    wceq
    @69
    @73
    @7
    @70
    csin
    @74
    fveq2d
    adantl
    @75
    @69
    @70
    @76
    resincld
    fvmptd
    fveq2d
    @69
    @77
    @105
    c1
    cle
    wbr
    @76
    @70
    abssinbd
    syl
    eqbrtrd
    syldan
    ralrimiva
    @98
    @101
    vb
    c1
    cr
    @78
    @96
    @100
    vy
    @97
    @44
    c1
    @95
    cle
    breq2
    ralbidv
    rspcev
    sylancr
    adantl
    vb
    vy
    @90
    @29
    bddmulibl
    syl3anc
    eqeltrd
    itgrecl
    sylan2
    @79
    @85
    pire
    a1i
    @80
    @85
    @81
    a1i
    redivcld
    fourierdlem22.b
    fmptd
    ffvelrnda
    ex
    jca
end
