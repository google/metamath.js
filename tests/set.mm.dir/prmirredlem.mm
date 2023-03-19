include "cn.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "c1.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "wne.mm"
include "zring.mm"
include "crg.mm"
include "zringring.mm"
include "zring1.mm"
include "irredn1.mm"
include "mpan.mm"
include "anim2i.mm"
include "eluz2b3.mm"
include "sylibr.mm"
include "cui.mm"
include "cdiv.mm"
include "co.mm"
include "cz.mm"
include "cmul.mm"
include "nnz.mm"
include "ad2antrl.mm"
include "simprr.mm"
include "cc0.mm"
include "wb.mm"
include "nnne0.mm"
include "ad2antrr.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "zcnd.mm"
include "cc.mm"
include "nncn.mm"
include "divcan2d.mm"
include "simplr.mm"
include "eqeltrd.mm"
include "zringbas.mm"
include "eqid.mm"
include "zringmulr.mm"
include "irredmul.mm"
include "cabs.mm"
include "zringunit.mm"
include "baib.mm"
include "syl.mm"
include "cn0.mm"
include "nnnn0.mm"
include "nn0re.mm"
include "nn0ge0.mm"
include "absidd.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "cr.mm"
include "nnre.mm"
include "simprl.mm"
include "nndivred.mm"
include "cle.mm"
include "clt.mm"
include "nnred.mm"
include "nngt0.mm"
include "divge0.mm"
include "syl22anc.mm"
include "1cnd.mm"
include "divmuld.mm"
include "mulid1d.mm"
include "3bitrd.mm"
include "orbi12d.mm"
include "expr.mm"
include "ralrimiva.mm"
include "isprm2.mm"
include "sylanbrc.mm"
include "wn.mm"
include "prmz.mm"
include "1nprm.mm"
include "prmnn.mm"
include "3syl.mm"
include "id.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "adantld.mm"
include "syl5bi.mm"
include "mtoi.mm"
include "simplrl.mm"
include "nnne0d.mm"
include "simpr.mm"
include "simplrr.mm"
include "mul02d.mm"
include "3netr4d.mm"
include "oveq1.mm"
include "necon3i.mm"
include "absne0d.mm"
include "neneqd.mm"
include "nn0abscl.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"
include "simprbi.mm"
include "dvdsmul1.mm"
include "ad2antlr.mm"
include "breqtrd.mm"
include "absdvdsb.mm"
include "syl2anc.mm"
include "breq1.mm"
include "eqeq1.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"
include "abscld.mm"
include "recnd.mm"
include "mulcand.mm"
include "fveq2d.mm"
include "absmuld.mm"
include "3eqtr3d.mm"
include "eqeq12d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "3bitr2d.mm"
include "mpbird.mm"
include "ex.mm"
include "ralrimivva.mm"
include "isirred2.mm"
include "syl3anbrc.mm"
include "adantl.mm"
include "impbida.mm"

theorem prmirredlem
  let cA: class A
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  assume prmirred.i: |- I = ( Irred ` ZZring )


  assert |- ( A e. NN -> ( A e. I <-> A e. Prime ) )

  proof
    cA
    cn
    wcel
    #
    cA
    cI
    wcel
    #
    cA
    cprime
    wcel
    #
    @0
    @1
    wa
    #
    cA
    c2
    cuz
    cfv
    wcel
    #
    vy
    cv
    #
    cA
    cdvds
    wbr
    #
    @5
    c1
    wceq
    #
    @5
    cA
    wceq
    #
    wo
    #
    wi
    #
    vy
    cn
    wral
    #
    @2
    @3
    @0
    cA
    c1
    wne
    #
    wa
    @4
    @1
    @12
    @0
    zring
    crg
    wcel
    @1
    @12
    zringring
    zring
    c1
    cI
    cA
    prmirred.i
    zring1
    irredn1
    mpan
    anim2i
    cA
    eluz2b3
    sylibr
    @3
    @10
    vy
    cn
    @3
    @5
    cn
    wcel
    #
    @6
    @9
    @3
    @13
    @6
    wa
    #
    wa
    #
    @5
    zring
    cui
    cfv
    #
    wcel
    #
    cA
    @5
    cdiv
    co
    #
    @16
    wcel
    #
    wo
    #
    @9
    @15
    @5
    cz
    wcel
    #
    @18
    cz
    wcel
    #
    @5
    @18
    cmul
    co
    #
    cI
    wcel
    @20
    @13
    @21
    @3
    @6
    @5
    nnz
    ad2antrl
    #
    @15
    @6
    @22
    @3
    @13
    @6
    simprr
    @15
    @21
    @5
    cc0
    wne
    #
    cA
    cz
    wcel
    #
    @6
    @22
    wb
    @24
    @13
    @25
    @3
    @6
    @5
    nnne0
    ad2antrl
    #
    @0
    @26
    @1
    @14
    cA
    nnz
    ad2antrr
    #
    @5
    cA
    dvdsval2
    syl3anc
    mpbid
    #
    @15
    @23
    cA
    cI
    @15
    cA
    @5
    @15
    cA
    @28
    zcnd
    #
    @13
    @5
    cc
    wcel
    @3
    @6
    @5
    nncn
    ad2antrl
    #
    @27
    divcan2d
    @0
    @1
    @14
    simplr
    eqeltrd
    cz
    zring
    cmul
    @16
    cI
    @5
    @18
    prmirred.i
    zringbas
    @16
    eqid
    #
    zringmulr
    irredmul
    syl3anc
    @15
    @17
    @7
    @19
    @8
    @15
    @17
    @5
    cabs
    cfv
    #
    c1
    wceq
    #
    @7
    @15
    @21
    @17
    @34
    wb
    #
    @24
    @17
    @21
    @34
    @5
    zringunit
    baib
    #
    syl
    @15
    @33
    @5
    c1
    @13
    @33
    @5
    wceq
    #
    @3
    @6
    @13
    @5
    cn0
    wcel
    #
    @37
    @5
    nnnn0
    @38
    @5
    @5
    nn0re
    @5
    nn0ge0
    absidd
    syl
    ad2antrl
    eqeq1d
    bitrd
    @15
    @19
    @18
    cabs
    cfv
    #
    c1
    wceq
    #
    @8
    @15
    @22
    @19
    @40
    wb
    @29
    @19
    @22
    @40
    @18
    zringunit
    baib
    syl
    @15
    @40
    @18
    c1
    wceq
    @5
    c1
    cmul
    co
    #
    cA
    wceq
    @8
    @15
    @39
    @18
    c1
    @15
    @18
    @15
    cA
    @5
    @0
    cA
    cr
    wcel
    #
    @1
    @14
    cA
    nnre
    ad2antrr
    #
    @3
    @13
    @6
    simprl
    #
    nndivred
    @15
    @42
    cc0
    cA
    cle
    wbr
    #
    @5
    cr
    wcel
    cc0
    @5
    clt
    wbr
    #
    cc0
    @18
    cle
    wbr
    @43
    @0
    @45
    @1
    @14
    @0
    cA
    cn0
    wcel
    #
    @45
    cA
    nnnn0
    #
    cA
    nn0ge0
    #
    syl
    ad2antrr
    @15
    @5
    @44
    nnred
    @13
    @46
    @3
    @6
    @5
    nngt0
    ad2antrl
    cA
    @5
    divge0
    syl22anc
    absidd
    eqeq1d
    @15
    cA
    @5
    c1
    @30
    @31
    @15
    1cnd
    @27
    divmuld
    @15
    @41
    @5
    cA
    @15
    @5
    @31
    mulid1d
    eqeq1d
    3bitrd
    bitrd
    orbi12d
    mpbid
    expr
    ralrimiva
    vy
    cA
    isprm2
    #
    sylanbrc
    @2
    @1
    @0
    @2
    @26
    cA
    @16
    wcel
    #
    wn
    vx
    cv
    #
    @5
    cmul
    co
    #
    cA
    wceq
    #
    @52
    @16
    wcel
    #
    @17
    wo
    #
    wi
    #
    vy
    cz
    wral
    vx
    cz
    wral
    @1
    cA
    prmz
    #
    @2
    @51
    c1
    cprime
    wcel
    #
    1nprm
    @51
    @26
    cA
    cabs
    cfv
    #
    c1
    wceq
    #
    wa
    @2
    @59
    cA
    zringunit
    @2
    @61
    @59
    @26
    @2
    @60
    cprime
    wcel
    @61
    @59
    @2
    @60
    cA
    cprime
    @2
    @0
    @47
    @60
    cA
    wceq
    #
    cA
    prmnn
    #
    @48
    @47
    cA
    cA
    nn0re
    @49
    absidd
    3syl
    #
    @2
    id
    eqeltrd
    @60
    c1
    cprime
    eleq1
    syl5ibcom
    adantld
    syl5bi
    mtoi
    @2
    @57
    vx
    vy
    cz
    cz
    @2
    @52
    cz
    wcel
    #
    @21
    wa
    #
    wa
    #
    @54
    @56
    @67
    @54
    wa
    #
    @56
    @52
    cabs
    cfv
    #
    c1
    wceq
    #
    @69
    cA
    wceq
    #
    wo
    #
    @68
    @69
    cn
    wcel
    #
    @11
    @69
    cA
    cdvds
    wbr
    #
    @72
    @68
    @73
    @69
    cc0
    wceq
    #
    @68
    @69
    cc0
    @68
    @52
    @68
    @52
    @2
    @65
    @21
    @54
    simplrl
    #
    zcnd
    #
    @68
    @53
    cc0
    @5
    cmul
    co
    #
    wne
    @52
    cc0
    wne
    @68
    cA
    cc0
    @53
    @78
    @68
    cA
    @2
    @0
    @66
    @54
    @63
    ad2antrr
    nnne0d
    @67
    @54
    simpr
    #
    @68
    @5
    @68
    @5
    @2
    @65
    @21
    @54
    simplrr
    #
    zcnd
    #
    mul02d
    3netr4d
    @52
    cc0
    @53
    @78
    @52
    cc0
    @5
    cmul
    oveq1
    necon3i
    syl
    absne0d
    #
    neneqd
    @68
    @73
    @75
    @68
    @69
    cn0
    wcel
    #
    @73
    @75
    wo
    @68
    @65
    @83
    @76
    @52
    nn0abscl
    syl
    @69
    elnn0
    sylib
    ord
    mt3d
    @2
    @11
    @66
    @54
    @2
    @4
    @11
    @50
    simprbi
    ad2antrr
    @68
    @52
    cA
    cdvds
    wbr
    #
    @74
    @68
    @52
    @53
    cA
    cdvds
    @66
    @52
    @53
    cdvds
    wbr
    @2
    @54
    @52
    @5
    dvdsmul1
    ad2antlr
    @79
    breqtrd
    @68
    @65
    @26
    @84
    @74
    wb
    @76
    @2
    @26
    @66
    @54
    @58
    ad2antrr
    @52
    cA
    absdvdsb
    syl2anc
    mpbid
    @10
    @74
    @72
    wi
    vy
    @69
    cn
    @5
    @69
    wceq
    #
    @6
    @74
    @9
    @72
    @5
    @69
    cA
    cdvds
    breq1
    @85
    @7
    @70
    @8
    @71
    @5
    @69
    c1
    eqeq1
    @5
    @69
    cA
    eqeq1
    orbi12d
    imbi12d
    rspcv
    syl3c
    @68
    @55
    @70
    @17
    @71
    @68
    @65
    @55
    @70
    wb
    @76
    @55
    @65
    @70
    @52
    zringunit
    baib
    syl
    @68
    @17
    @34
    @69
    @33
    cmul
    co
    #
    @69
    c1
    cmul
    co
    #
    wceq
    #
    @71
    @68
    @21
    @35
    @80
    @36
    syl
    @68
    @33
    c1
    @69
    @68
    @33
    @68
    @5
    @81
    abscld
    recnd
    @68
    1cnd
    @68
    @69
    @68
    @52
    @77
    abscld
    recnd
    #
    @82
    mulcand
    @68
    @88
    cA
    @69
    wceq
    @71
    @68
    @86
    cA
    @87
    @69
    @68
    @53
    cabs
    cfv
    @60
    @86
    cA
    @68
    @53
    cA
    cabs
    @79
    fveq2d
    @68
    @52
    @5
    @77
    @81
    absmuld
    @2
    @62
    @66
    @54
    @64
    ad2antrr
    3eqtr3d
    @68
    @69
    @89
    mulid1d
    eqeq12d
    cA
    @69
    eqcom
    syl6bb
    3bitr2d
    orbi12d
    mpbird
    ex
    ralrimivva
    vx
    vy
    cz
    zring
    cmul
    @16
    cI
    cA
    zringbas
    @32
    prmirred.i
    zringmulr
    isirred2
    syl3anbrc
    adantl
    impbida
end
