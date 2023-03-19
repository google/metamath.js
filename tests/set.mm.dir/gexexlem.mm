include "cfv.mm"
include "cn0.mm"
include "wcel.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "odcl.mm"
include "syl.mm"
include "nnnn0d.mm"
include "cgrp.mm"
include "cabl.mm"
include "ablgrp.mm"
include "gexod.mm"
include "syl2anc.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "cpc.mm"
include "co.mm"
include "cle.mm"
include "cprime.mm"
include "cexp.mm"
include "cdiv.mm"
include "cmul.mm"
include "cmg.mm"
include "cplusg.mm"
include "cgcd.mm"
include "c1.mm"
include "ad2antrr.mm"
include "cz.mm"
include "cn.mm"
include "prmnn.mm"
include "adantl.mm"
include "simpr.mm"
include "gexnnod.mm"
include "syl3anc.mm"
include "pccld.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "eqid.mm"
include "mulgcl.mm"
include "simplr.mm"
include "pcdvds.mm"
include "wb.mm"
include "nndivdvds.mm"
include "mpbid.mm"
include "odmulg.mm"
include "gcdeq.mm"
include "mpbird.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan3d.mm"
include "eqtr2d.mm"
include "divcan1d.mm"
include "dvdsmul1.mm"
include "breqtrd.mm"
include "3eqtrrd.mm"
include "mulcanad.mm"
include "oveq12d.mm"
include "gcdcom.mm"
include "wn.mm"
include "pcndvds2.mm"
include "coprm.mm"
include "wi.mm"
include "prmz.mm"
include "rpexp1i.mm"
include "mpd.mm"
include "3eqtrd.mm"
include "odadd.mm"
include "syl31anc.mm"
include "grpcl.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "breq1d.mm"
include "rspcv.mm"
include "sylc.mm"
include "eqbrtrrd.mm"
include "nnred.mm"
include "nnrpd.mm"
include "lemuldivd.mm"
include "crp.mm"
include "nnrp.mm"
include "cr.mm"
include "cc0.mm"
include "clt.mm"
include "rpregt0.mm"
include "lediv2.mm"
include "syl3an.mm"
include "nn0zd.mm"
include "c2.mm"
include "cuz.mm"
include "prmuz2.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "leexp2d.mm"
include "adantr.mm"
include "pc2dvds.mm"
include "gexdvds2.mm"
include "dvdseq.mm"
include "syl22anc.mm"

theorem gexexlem
  let wph: wff ph
  let vy: setvar y
  let cA: class A
  let cE: class E
  let cG: class G
  let cO: class O
  let cX: class X
  let vp: setvar p
  let vx: setvar x
  let vn: setvar n
  assume gexex.1: |- X = ( Base ` G )
  assume gexex.2: |- E = ( gEx ` G )
  assume gexex.3: |- O = ( od ` G )
  assume gexexlem.1: |- ( ph -> G e. Abel )
  assume gexexlem.2: |- ( ph -> E e. NN )
  assume gexexlem.3: |- ( ph -> A e. X )
  assume gexexlem.4: |- ( ( ph /\ y e. X ) -> ( O ` y ) <_ ( O ` A ) )

  disjoint A y
  disjoint E y
  disjoint G y
  disjoint O y
  disjoint ph y
  disjoint X y
  disjoint p x
  disjoint p y
  disjoint A p
  disjoint x y
  disjoint A x
  disjoint n x
  disjoint n y
  disjoint E n
  disjoint E x
  disjoint G x
  disjoint n p
  disjoint O n
  disjoint O p
  disjoint O x
  disjoint p ph
  disjoint ph x
  disjoint X p
  disjoint X x
  assert |- ( ph -> ( O ` A ) = E )

  proof
    wph
    cA
    cO
    cfv
    #
    cn0
    wcel
    #
    cE
    cn0
    wcel
    @0
    cE
    cdvds
    wbr
    #
    cE
    @0
    cdvds
    wbr
    #
    @0
    cE
    wceq
    wph
    cA
    cX
    wcel
    #
    @1
    gexexlem.3
    cA
    cG
    cO
    cX
    gexex.1
    gexex.3
    odcl
    syl
    #
    wph
    cE
    gexexlem.2
    nnnn0d
    wph
    cG
    cgrp
    wcel
    #
    @4
    @2
    wph
    cG
    cabl
    wcel
    #
    @6
    gexexlem.1
    cG
    ablgrp
    syl
    #
    gexexlem.3
    cA
    cE
    cG
    cO
    cX
    gexex.1
    gexex.2
    gexex.3
    gexod
    syl2anc
    wph
    @3
    vx
    cv
    #
    cO
    cfv
    #
    @0
    cdvds
    wbr
    #
    vx
    cX
    wral
    #
    wph
    @11
    vx
    cX
    wph
    @9
    cX
    wcel
    #
    wa
    #
    @11
    vp
    cv
    #
    @10
    cpc
    co
    #
    @15
    @0
    cpc
    co
    #
    cle
    wbr
    #
    vp
    cprime
    wral
    #
    @14
    @18
    vp
    cprime
    @14
    @15
    cprime
    wcel
    #
    wa
    #
    @18
    @15
    @16
    cexp
    co
    #
    @15
    @17
    cexp
    co
    #
    cle
    wbr
    #
    @21
    @24
    @0
    @23
    cdiv
    co
    #
    @0
    @22
    cdiv
    co
    cle
    wbr
    #
    @21
    @25
    @22
    cmul
    co
    #
    @0
    cle
    wbr
    @26
    @21
    @23
    cA
    cG
    cmg
    cfv
    #
    co
    #
    @10
    @22
    cdiv
    co
    #
    @9
    @28
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cO
    cfv
    #
    @27
    @0
    cle
    @21
    @34
    @29
    cO
    cfv
    #
    @31
    cO
    cfv
    #
    cmul
    co
    #
    @27
    @21
    @7
    @29
    cX
    wcel
    #
    @31
    cX
    wcel
    #
    @35
    @36
    cgcd
    co
    #
    c1
    wceq
    @34
    @37
    wceq
    wph
    @7
    @13
    @20
    gexexlem.1
    ad2antrr
    @21
    @6
    @23
    cz
    wcel
    #
    @4
    @38
    wph
    @6
    @13
    @20
    @8
    ad2antrr
    #
    @21
    @23
    @21
    @15
    @17
    @20
    @15
    cn
    wcel
    #
    @14
    @15
    prmnn
    adantl
    #
    @21
    @15
    @0
    @14
    @20
    simpr
    #
    @21
    @6
    cE
    cn
    wcel
    #
    @4
    @0
    cn
    wcel
    #
    @42
    wph
    @46
    @13
    @20
    gexexlem.2
    ad2antrr
    #
    wph
    @4
    @13
    @20
    gexexlem.3
    ad2antrr
    #
    cA
    cE
    cG
    cO
    cX
    gexex.1
    gexex.2
    gexex.3
    gexnnod
    syl3anc
    #
    pccld
    #
    nnexpcld
    #
    nnzd
    #
    @49
    cX
    @28
    cG
    @23
    cA
    gexex.1
    @28
    eqid
    #
    mulgcl
    syl3anc
    #
    @21
    @6
    @30
    cz
    wcel
    #
    @13
    @39
    @42
    @21
    @30
    @21
    @22
    @10
    cdvds
    wbr
    #
    @30
    cn
    wcel
    #
    @21
    @20
    @10
    cn
    wcel
    #
    @57
    @45
    @21
    @6
    @46
    @13
    @59
    @42
    @48
    wph
    @13
    @20
    simplr
    #
    @9
    cE
    cG
    cO
    cX
    gexex.1
    gexex.2
    gexex.3
    gexnnod
    syl3anc
    #
    @15
    @10
    pcdvds
    syl2anc
    @21
    @59
    @22
    cn
    wcel
    #
    @57
    @58
    wb
    @61
    @21
    @15
    @16
    @44
    @21
    @15
    @10
    @45
    @61
    pccld
    #
    nnexpcld
    #
    @10
    @22
    nndivdvds
    syl2anc
    mpbid
    #
    nnzd
    #
    @60
    cX
    @28
    cG
    @30
    @9
    gexex.1
    @54
    mulgcl
    syl3anc
    #
    @21
    @40
    @25
    @22
    cgcd
    co
    #
    @22
    @25
    cgcd
    co
    #
    c1
    @21
    @35
    @25
    @36
    @22
    cgcd
    @21
    @25
    @23
    @35
    cmul
    co
    #
    @23
    cdiv
    co
    @35
    @21
    @0
    @70
    @23
    cdiv
    @21
    @0
    @23
    @0
    cgcd
    co
    #
    @35
    cmul
    co
    #
    @70
    @21
    @6
    @4
    @41
    @0
    @72
    wceq
    @42
    @49
    @53
    cA
    @28
    cG
    @23
    cO
    cX
    gexex.1
    gexex.3
    @54
    odmulg
    syl3anc
    @21
    @71
    @23
    @35
    cmul
    @21
    @71
    @23
    wceq
    #
    @23
    @0
    cdvds
    wbr
    #
    @21
    @20
    @47
    @74
    @45
    @50
    @15
    @0
    pcdvds
    syl2anc
    #
    @21
    @23
    cn
    wcel
    #
    @47
    @73
    @74
    wb
    @52
    @50
    @23
    @0
    gcdeq
    syl2anc
    mpbird
    oveq1d
    eqtrd
    oveq1d
    @21
    @35
    @23
    @21
    @35
    @21
    @6
    @46
    @38
    @35
    cn
    wcel
    @42
    @48
    @55
    @29
    cE
    cG
    cO
    cX
    gexex.1
    gexex.2
    gexex.3
    gexnnod
    syl3anc
    nncnd
    @21
    @23
    @52
    nncnd
    @21
    @23
    @52
    nnne0d
    divcan3d
    eqtr2d
    #
    @21
    @36
    @22
    @30
    @21
    @36
    @21
    @6
    @46
    @39
    @36
    cn
    wcel
    @42
    @48
    @67
    @31
    cE
    cG
    cO
    cX
    gexex.1
    gexex.2
    gexex.3
    gexnnod
    syl3anc
    nncnd
    @21
    @22
    @64
    nncnd
    #
    @21
    @30
    @65
    nncnd
    @21
    @30
    @65
    nnne0d
    @21
    @30
    @22
    cmul
    co
    #
    @10
    @30
    @10
    cgcd
    co
    #
    @36
    cmul
    co
    #
    @30
    @36
    cmul
    co
    @21
    @10
    @22
    @21
    @10
    @61
    nncnd
    @78
    @21
    @22
    @64
    nnne0d
    divcan1d
    #
    @21
    @6
    @13
    @56
    @10
    @81
    wceq
    @42
    @60
    @66
    @9
    @28
    cG
    @30
    cO
    cX
    gexex.1
    gexex.3
    @54
    odmulg
    syl3anc
    @21
    @80
    @30
    @36
    cmul
    @21
    @80
    @30
    wceq
    #
    @30
    @10
    cdvds
    wbr
    #
    @21
    @30
    @79
    @10
    cdvds
    @21
    @56
    @22
    cz
    wcel
    #
    @30
    @79
    cdvds
    wbr
    @66
    @21
    @22
    @64
    nnzd
    #
    @30
    @22
    dvdsmul1
    syl2anc
    @82
    breqtrd
    @21
    @58
    @59
    @83
    @84
    wb
    @65
    @61
    @30
    @10
    gcdeq
    syl2anc
    mpbird
    oveq1d
    3eqtrrd
    mulcanad
    #
    oveq12d
    @21
    @25
    cz
    wcel
    #
    @85
    @68
    @69
    wceq
    @21
    @25
    @21
    @74
    @25
    cn
    wcel
    #
    @75
    @21
    @47
    @76
    @74
    @89
    wb
    @50
    @52
    @0
    @23
    nndivdvds
    syl2anc
    mpbid
    #
    nnzd
    #
    @86
    @25
    @22
    gcdcom
    syl2anc
    @21
    @15
    @25
    cgcd
    co
    c1
    wceq
    #
    @69
    c1
    wceq
    #
    @21
    @15
    @25
    cdvds
    wbr
    wn
    #
    @92
    @21
    @20
    @47
    @94
    @45
    @50
    @15
    @0
    pcndvds2
    syl2anc
    @21
    @20
    @88
    @94
    @92
    wb
    @45
    @91
    @15
    @25
    coprm
    syl2anc
    mpbid
    @21
    @15
    cz
    wcel
    #
    @88
    @16
    cn0
    wcel
    @92
    @93
    wi
    @20
    @95
    @14
    @15
    prmz
    adantl
    @91
    @63
    @15
    @25
    @16
    rpexp1i
    syl3anc
    mpd
    3eqtrd
    @29
    @31
    @32
    cG
    cO
    cX
    gexex.3
    gexex.1
    @32
    eqid
    #
    odadd
    syl31anc
    @21
    @35
    @25
    @36
    @22
    cmul
    @77
    @87
    oveq12d
    eqtrd
    @21
    @33
    cX
    wcel
    #
    vy
    cv
    #
    cO
    cfv
    #
    @0
    cle
    wbr
    #
    vy
    cX
    wral
    #
    @34
    @0
    cle
    wbr
    #
    @21
    @6
    @38
    @39
    @97
    @42
    @55
    @67
    cX
    @32
    cG
    @29
    @31
    gexex.1
    @96
    grpcl
    syl3anc
    wph
    @101
    @13
    @20
    wph
    @100
    vy
    cX
    gexexlem.4
    ralrimiva
    ad2antrr
    @100
    @102
    vy
    @33
    cX
    @98
    @33
    wceq
    @99
    @34
    @0
    cle
    @98
    @33
    cO
    fveq2
    breq1d
    rspcv
    sylc
    eqbrtrrd
    @21
    @25
    @0
    @22
    @21
    @25
    @90
    nnred
    @21
    @0
    @50
    nnred
    @21
    @22
    @64
    nnrpd
    lemuldivd
    mpbid
    @21
    @62
    @76
    @47
    @24
    @26
    wb
    #
    @64
    @52
    @50
    @62
    @22
    crp
    wcel
    #
    @76
    @23
    crp
    wcel
    #
    @47
    @0
    crp
    wcel
    #
    @103
    @22
    nnrp
    @23
    nnrp
    @0
    nnrp
    @104
    @22
    cr
    wcel
    cc0
    @22
    clt
    wbr
    wa
    @105
    @23
    cr
    wcel
    cc0
    @23
    clt
    wbr
    wa
    @106
    @0
    cr
    wcel
    cc0
    @0
    clt
    wbr
    wa
    @103
    @22
    rpregt0
    @23
    rpregt0
    @0
    rpregt0
    @22
    @23
    @0
    lediv2
    syl3an
    syl3an
    syl3anc
    mpbird
    @21
    @15
    @16
    @17
    @21
    @15
    @44
    nnred
    @21
    @16
    @63
    nn0zd
    @21
    @17
    @51
    nn0zd
    @21
    @15
    c2
    cuz
    cfv
    wcel
    #
    c1
    @15
    clt
    wbr
    #
    @20
    @107
    @14
    @15
    prmuz2
    adantl
    @107
    @43
    @108
    @15
    eluz2b2
    simprbi
    syl
    leexp2d
    mpbird
    ralrimiva
    @14
    @10
    cz
    wcel
    @0
    cz
    wcel
    #
    @11
    @19
    wb
    @14
    @10
    @13
    @10
    cn0
    wcel
    wph
    @9
    cG
    cO
    cX
    gexex.1
    gexex.3
    odcl
    adantl
    nn0zd
    wph
    @109
    @13
    wph
    @0
    @5
    nn0zd
    #
    adantr
    @10
    @0
    vp
    pc2dvds
    syl2anc
    mpbird
    ralrimiva
    wph
    @6
    @109
    @3
    @12
    wb
    @8
    @110
    vx
    cE
    cG
    @0
    cO
    cX
    gexex.1
    gexex.2
    gexex.3
    gexdvds2
    syl2anc
    mpbird
    @0
    cE
    dvdseq
    syl22anc
end
