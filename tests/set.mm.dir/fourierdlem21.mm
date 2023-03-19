include "cfv.mm"
include "cr.mm"
include "wcel.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "csin.mm"
include "cmpt.mm"
include "cibl.mm"
include "citg.mm"
include "cn.mm"
include "cpi.mm"
include "cdiv.mm"
include "wa.mm"
include "cn0.mm"
include "nnnn0.mm"
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
include "resincld.mm"
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
include "sincn.mm"
include "wss.mm"
include "eqsstri.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "ssid.mm"
include "constcncfg.mm"
include "idcncfg.mm"
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
include "abssinbd.mm"
include "eqbrtrd.mm"
include "syldan.mm"
include "ralrimiva.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "bddmulibl.mm"
include "syl3anc.mm"
include "itgrecl.mm"
include "sylan2.mm"
include "pire.mm"
include "cc0.mm"
include "wne.mm"
include "0re.mm"
include "pipos.mm"
include "gtneii.mm"
include "redivcld.mm"
include "fmptd.mm"
include "nnnn0d.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "simpl.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "vtoclg.mm"
include "anabsi7.mm"
include "mpdan.mm"
include "ancli.mm"
include "itgeq2dv.mm"
include "sylc.mm"
include "jca31.mm"

theorem fourierdlem21
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cC: class C
  let vn: setvar n
  let cF: class F
  let cN: class N
  let vb: setvar b
  let vy: setvar y
  let vk: setvar k
  assume fourierdlem21.f: |- ( ph -> F : RR --> RR )
  assume fourierdlem21.c: |- C = ( -u _pi (,) _pi )
  assume fourierdlem21.fibl: |- ( ph -> ( F |` C ) e. L^1 )
  assume fourierdlem21.b: |- B = ( n e. NN |-> ( S. C ( ( F ` x ) x. ( sin ` ( n x. x ) ) ) _d x / _pi ) )
  assume fourierdlem21.n: |- ( ph -> N e. NN )

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
  assert |- ( ph -> ( ( ( B ` N ) e. RR /\ ( x e. C |-> ( ( F ` x ) x. ( sin ` ( N x. x ) ) ) ) e. L^1 ) /\ S. C ( ( F ` x ) x. ( sin ` ( N x. x ) ) ) _d x e. RR ) )

  proof
    wph
    cN
    cB
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
    cN
    @0
    cmul
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cibl
    wcel
    #
    vx
    cC
    @4
    citg
    #
    cr
    wcel
    #
    wph
    cn
    cr
    cN
    cB
    wph
    vn
    cn
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
    @9
    cn
    wcel
    #
    wa
    #
    @13
    cpi
    @14
    wph
    @9
    cn0
    wcel
    #
    @13
    cr
    wcel
    #
    @9
    nnnn0
    wph
    @16
    wa
    #
    vx
    cC
    @12
    @18
    @0
    cC
    wcel
    #
    wa
    #
    @1
    @11
    wph
    @19
    @1
    cr
    wcel
    @16
    wph
    @19
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
    @19
    fourierdlem21.f
    adantr
    @19
    @0
    cr
    wcel
    #
    wph
    @19
    cpi
    cneg
    #
    cpi
    cioo
    co
    #
    cr
    @0
    @22
    cpi
    ioossre
    #
    @19
    @0
    cC
    @23
    @19
    id
    fourierdlem21.c
    syl6eleq
    sseldi
    #
    adantl
    ffvelrnd
    adantlr
    #
    @16
    @19
    @11
    cr
    wcel
    #
    wph
    @16
    @19
    wa
    #
    @10
    @28
    @9
    @0
    @16
    @9
    cr
    wcel
    #
    @19
    @9
    nn0re
    #
    adantr
    @19
    @21
    @16
    @25
    adantl
    remulcld
    resincld
    #
    adantll
    #
    remulcld
    @18
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
    vx
    cC
    @1
    cmpt
    #
    cmul
    cof
    co
    #
    cibl
    @18
    @36
    vx
    cC
    @11
    @1
    cmul
    co
    #
    cmpt
    @33
    @18
    vx
    cC
    @11
    @1
    cmul
    @34
    @35
    cvol
    cdm
    #
    cr
    cr
    cC
    @38
    wcel
    #
    @18
    cC
    @23
    @38
    fourierdlem21.c
    @22
    cpi
    ioombl
    eqeltri
    #
    a1i
    @32
    @26
    @18
    @34
    eqidd
    @18
    @35
    eqidd
    offval2
    @18
    vx
    cC
    @37
    @12
    @20
    @11
    @1
    @20
    @11
    @32
    recnd
    @20
    @1
    @26
    recnd
    mulcomd
    mpteq2dva
    eqtr2d
    @18
    @34
    cmbf
    wcel
    #
    @35
    cibl
    wcel
    #
    vy
    cv
    #
    @34
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
    @34
    cdm
    #
    wral
    #
    vb
    cr
    wrex
    #
    @36
    cibl
    wcel
    @18
    @39
    @34
    cC
    cc
    ccncf
    co
    #
    wcel
    @41
    @40
    @18
    vx
    @10
    csin
    cC
    csin
    cc
    cc
    ccncf
    co
    wcel
    @18
    sincn
    a1i
    @16
    vx
    cC
    @10
    cmpt
    @51
    wcel
    wph
    @16
    vx
    @9
    @0
    cC
    @16
    vx
    cC
    @9
    cc
    cC
    cc
    wss
    @16
    cC
    cr
    cc
    cC
    @23
    cr
    fourierdlem21.c
    @24
    eqsstri
    #
    ax-resscn
    sstri
    a1i
    #
    @16
    @9
    @30
    recnd
    cc
    cc
    wss
    @16
    cc
    ssid
    a1i
    #
    constcncfg
    @16
    vx
    cC
    cc
    @53
    @54
    idcncfg
    mulcncf
    adantl
    cncfmpt1f
    cC
    @34
    cnmbf
    sylancr
    wph
    @42
    @16
    wph
    @35
    cF
    cC
    cres
    #
    cibl
    wph
    @55
    vx
    cr
    @1
    cmpt
    #
    cC
    cres
    #
    @35
    wph
    cF
    @56
    cC
    wph
    vx
    cr
    cr
    cF
    fourierdlem21.f
    feqmptd
    reseq1d
    cC
    cr
    wss
    @57
    @35
    wceq
    wph
    @52
    vx
    cr
    cC
    @1
    resmpt
    mp1i
    eqtr2d
    fourierdlem21.fibl
    eqeltrd
    adantr
    @16
    @50
    wph
    @16
    c1
    cr
    wcel
    @45
    c1
    cle
    wbr
    #
    vy
    @48
    wral
    #
    @50
    1re
    @16
    @58
    vy
    @48
    @16
    @43
    @48
    wcel
    #
    @43
    cC
    wcel
    #
    @58
    @16
    @60
    wa
    #
    @43
    @48
    cC
    @16
    @60
    simpr
    @62
    @27
    vx
    cC
    wral
    @48
    cC
    wceq
    @62
    @27
    vx
    cC
    @16
    @60
    vx
    @16
    vx
    nfv
    vx
    vy
    @48
    vx
    @34
    vx
    cC
    @11
    nfmpt1
    nfdm
    nfcri
    nfan
    @16
    @19
    @27
    wi
    @60
    @16
    @19
    @27
    @31
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
    @16
    @61
    wa
    #
    @45
    @9
    @43
    cmul
    co
    #
    csin
    cfv
    #
    cabs
    cfv
    #
    c1
    cle
    @63
    @44
    @65
    cabs
    @63
    vx
    @43
    @11
    @65
    cC
    @34
    cr
    @63
    @34
    eqidd
    @0
    @43
    wceq
    #
    @11
    @65
    wceq
    @63
    @67
    @10
    @64
    csin
    @0
    @43
    @9
    cmul
    oveq2
    fveq2d
    adantl
    @16
    @61
    simpr
    #
    @63
    @64
    @63
    @9
    @43
    @16
    @29
    @61
    @30
    adantr
    @63
    cC
    cr
    @43
    @52
    @68
    sseldi
    remulcld
    #
    resincld
    fvmptd
    fveq2d
    @63
    @64
    cr
    wcel
    @66
    c1
    cle
    wbr
    @69
    @64
    abssinbd
    syl
    eqbrtrd
    syldan
    ralrimiva
    @49
    @59
    vb
    c1
    cr
    @46
    c1
    wceq
    @47
    @58
    vy
    @48
    @46
    c1
    @45
    cle
    breq2
    ralbidv
    rspcev
    sylancr
    adantl
    vb
    vy
    @34
    @35
    bddmulibl
    syl3anc
    eqeltrd
    #
    itgrecl
    sylan2
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
    fourierdlem21.b
    fmptd
    fourierdlem21.n
    ffvelrnd
    wph
    cN
    cn0
    wcel
    #
    @6
    wph
    cN
    fourierdlem21.n
    nnnn0d
    wph
    @72
    @6
    @18
    @33
    cibl
    wcel
    #
    wi
    wph
    @72
    wa
    #
    @6
    wi
    vn
    cN
    cn0
    @9
    cN
    wceq
    #
    @18
    @74
    @73
    @6
    @75
    @16
    @72
    wph
    @9
    cN
    cn0
    eleq1
    anbi2d
    @75
    @33
    @5
    cibl
    @75
    vx
    cC
    @12
    @4
    @75
    @19
    wa
    #
    @11
    @3
    @1
    cmul
    @76
    @10
    @2
    csin
    @76
    @9
    cN
    @0
    cmul
    @75
    @19
    simpl
    oveq1d
    fveq2d
    oveq2d
    #
    mpteq2dva
    eleq1d
    imbi12d
    @70
    vtoclg
    anabsi7
    mpdan
    wph
    cN
    cn
    wcel
    #
    wph
    @78
    wa
    #
    @8
    fourierdlem21.n
    wph
    @78
    fourierdlem21.n
    ancli
    @15
    @17
    wi
    @79
    @8
    wi
    vn
    cN
    cn
    @75
    @15
    @79
    @17
    @8
    @75
    @14
    @78
    wph
    @9
    cN
    cn
    eleq1
    anbi2d
    @75
    @13
    @7
    cr
    @75
    vx
    cC
    @12
    @4
    @77
    itgeq2dv
    eleq1d
    imbi12d
    @71
    vtoclg
    sylc
    jca31
end
