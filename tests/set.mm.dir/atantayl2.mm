include "cc.mm"
include "wcel.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "caddc.mm"
include "cseq.mm"
include "cn.mm"
include "ci.mm"
include "cneg.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "cmul.mm"
include "c2.mm"
include "cdiv.mm"
include "cmpt.mm"
include "catan.mm"
include "cli.mm"
include "cdvds.mm"
include "cc0.mm"
include "cif.mm"
include "ax-icn.mm"
include "negcli.mm"
include "a1i.mm"
include "cn0.mm"
include "nnnn0.mm"
include "ad2antlr.mm"
include "expcld.mm"
include "wceq.mm"
include "sqneg.mm"
include "ax-mp.mm"
include "oveq1i.mm"
include "wne.mm"
include "cz.mm"
include "ine0.mm"
include "negne0i.mm"
include "2z.mm"
include "wb.mm"
include "2ne0.mm"
include "nnz.mm"
include "adantl.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "biimpa.mm"
include "expmulz.mm"
include "syl22anc.mm"
include "3eqtr4a.mm"
include "nncn.mm"
include "2cnd.mm"
include "divcan2d.mm"
include "oveq2d.mm"
include "3eqtr3d.mm"
include "subeq0bd.mm"
include "it0e0.mm"
include "syl6eq.mm"
include "oveq1d.mm"
include "2cn.mm"
include "div0i.mm"
include "simplll.mm"
include "nnne0.mm"
include "divcld.mm"
include "mul02d.mm"
include "eqtr2d.mm"
include "wn.mm"
include "ax-1cn.mm"
include "neg1ne0.mm"
include "peano2cn.mm"
include "syl.mm"
include "divsubdird.mm"
include "2div2e1.mm"
include "oveq2i.mm"
include "df-2.mm"
include "pnpcan2d.mm"
include "syl5eq.mm"
include "eqtr3d.mm"
include "notbid.mm"
include "wo.mm"
include "zeo.mm"
include "ord.mm"
include "sylbid.mm"
include "imp.mm"
include "peano2zm.mm"
include "eqeltrrd.mm"
include "expclzd.mm"
include "2timesd.mm"
include "subcl.mm"
include "sylancl.mm"
include "expm1d.mm"
include "eqtrd.mm"
include "expcl.mm"
include "sylancr.mm"
include "divrec2d.mm"
include "i2.mm"
include "eqtri.mm"
include "irec.mm"
include "negeqi.mm"
include "divneg2.mm"
include "mp3an.mm"
include "negnegi.mm"
include "3eqtr3i.mm"
include "3eqtr3g.mm"
include "mulneg1.mm"
include "oveq12d.mm"
include "mulcl.mm"
include "negsubd.mm"
include "subdid.mm"
include "eqtr4d.mm"
include "3eqtrd.mm"
include "mvllmuld.mm"
include "ifeqda.mm"
include "mpteq2dva.mm"
include "seqeq3d.mm"
include "eqid.mm"
include "atantayl.mm"
include "eqbrtrd.mm"

theorem atantayl2
  let cA: class A
  let vn: setvar n
  let cF: class F
  assume atantayl2.1: |- F = ( n e. NN |-> if ( 2 || n , 0 , ( ( -u 1 ^ ( ( n - 1 ) / 2 ) ) x. ( ( A ^ n ) / n ) ) ) )

  disjoint A n
  assert |- ( ( A e. CC /\ ( abs ` A ) < 1 ) -> seq 1 ( + , F ) ~~> ( arctan ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cabs
    cfv
    c1
    clt
    wbr
    #
    wa
    #
    caddc
    cF
    c1
    cseq
    caddc
    vn
    cn
    ci
    ci
    cneg
    #
    vn
    cv
    #
    cexp
    co
    #
    ci
    @4
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    c2
    cdiv
    co
    #
    cA
    @4
    cexp
    co
    #
    @4
    cdiv
    co
    #
    cmul
    co
    #
    cmpt
    #
    c1
    cseq
    cA
    catan
    cfv
    cli
    @2
    cF
    @13
    caddc
    c1
    @2
    cF
    vn
    cn
    c2
    @4
    cdvds
    wbr
    #
    cc0
    c1
    cneg
    #
    @4
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cexp
    co
    #
    @11
    cmul
    co
    #
    cif
    #
    cmpt
    @13
    atantayl2.1
    @2
    vn
    cn
    @20
    @12
    @2
    @4
    cn
    wcel
    #
    wa
    #
    @14
    cc0
    @19
    @12
    @22
    @14
    wa
    #
    @12
    cc0
    @11
    cmul
    co
    cc0
    @23
    @9
    cc0
    @11
    cmul
    @23
    @9
    cc0
    c2
    cdiv
    co
    cc0
    @23
    @8
    cc0
    c2
    cdiv
    @23
    @8
    ci
    cc0
    cmul
    co
    cc0
    @23
    @7
    cc0
    ci
    cmul
    @23
    @5
    @6
    @23
    @3
    @4
    @3
    cc
    wcel
    #
    @23
    ci
    ax-icn
    negcli
    #
    a1i
    #
    @21
    @4
    cn0
    wcel
    #
    @2
    @14
    @4
    nnnn0
    #
    ad2antlr
    #
    expcld
    @23
    @3
    c2
    @4
    c2
    cdiv
    co
    #
    cmul
    co
    #
    cexp
    co
    #
    ci
    @31
    cexp
    co
    #
    @5
    @6
    @23
    @3
    c2
    cexp
    co
    #
    @30
    cexp
    co
    #
    ci
    c2
    cexp
    co
    #
    @30
    cexp
    co
    #
    @32
    @33
    @34
    @36
    @30
    cexp
    ci
    cc
    wcel
    #
    @34
    @36
    wceq
    ax-icn
    ci
    sqneg
    ax-mp
    #
    oveq1i
    @23
    @24
    @3
    cc0
    wne
    #
    c2
    cz
    wcel
    #
    @30
    cz
    wcel
    #
    @32
    @35
    wceq
    @26
    @40
    @23
    ci
    ax-icn
    ine0
    negne0i
    #
    a1i
    @41
    @23
    2z
    a1i
    #
    @22
    @14
    @42
    @22
    @41
    c2
    cc0
    wne
    #
    @4
    cz
    wcel
    #
    @14
    @42
    wb
    @41
    @22
    2z
    a1i
    @45
    @22
    2ne0
    a1i
    @21
    @46
    @2
    @4
    nnz
    #
    adantl
    #
    c2
    @4
    dvdsval2
    syl3anc
    #
    biimpa
    #
    @3
    c2
    @30
    expmulz
    syl22anc
    @23
    @38
    ci
    cc0
    wne
    #
    @41
    @42
    @33
    @37
    wceq
    @38
    @23
    ax-icn
    a1i
    @51
    @23
    ine0
    a1i
    @44
    @50
    ci
    c2
    @30
    expmulz
    syl22anc
    3eqtr4a
    @23
    @31
    @4
    @3
    cexp
    @23
    @4
    c2
    @21
    @4
    cc
    wcel
    #
    @2
    @14
    @4
    nncn
    #
    ad2antlr
    #
    @23
    2cnd
    @45
    @23
    2ne0
    a1i
    divcan2d
    #
    oveq2d
    @23
    @31
    @4
    ci
    cexp
    @55
    oveq2d
    3eqtr3d
    subeq0bd
    oveq2d
    it0e0
    syl6eq
    oveq1d
    c2
    2cn
    2ne0
    div0i
    syl6eq
    oveq1d
    @23
    @11
    @23
    @10
    @4
    @23
    cA
    @4
    @0
    @1
    @21
    @14
    simplll
    @29
    expcld
    @54
    @21
    @4
    cc0
    wne
    @2
    @14
    @4
    nnne0
    ad2antlr
    divcld
    mul02d
    eqtr2d
    @22
    @14
    wn
    #
    wa
    #
    @18
    @9
    @11
    cmul
    @57
    c2
    @18
    @8
    @57
    2cnd
    #
    @57
    @15
    @17
    @15
    cc
    wcel
    @57
    c1
    ax-1cn
    negcli
    a1i
    @15
    cc0
    wne
    @57
    neg1ne0
    a1i
    @57
    @4
    c1
    caddc
    co
    #
    c2
    cdiv
    co
    #
    c1
    cmin
    co
    #
    @17
    cz
    @57
    @59
    c2
    cmin
    co
    #
    c2
    cdiv
    co
    #
    @61
    @17
    @57
    @63
    @60
    c2
    c2
    cdiv
    co
    #
    cmin
    co
    @61
    @57
    @59
    c2
    c2
    @57
    @52
    @59
    cc
    wcel
    @21
    @52
    @2
    @56
    @53
    ad2antlr
    #
    @4
    peano2cn
    syl
    @58
    @58
    @45
    @57
    2ne0
    a1i
    #
    divsubdird
    @64
    c1
    @60
    cmin
    2div2e1
    oveq2i
    syl6eq
    @57
    @62
    @16
    c2
    cdiv
    @57
    @62
    @59
    c1
    c1
    caddc
    co
    #
    cmin
    co
    @16
    c2
    @67
    @59
    cmin
    df-2
    oveq2i
    @57
    @4
    c1
    c1
    @65
    c1
    cc
    wcel
    #
    @57
    ax-1cn
    a1i
    #
    @69
    pnpcan2d
    syl5eq
    oveq1d
    eqtr3d
    @57
    @60
    cz
    wcel
    #
    @61
    cz
    wcel
    @22
    @56
    @70
    @22
    @56
    @42
    wn
    @70
    @22
    @14
    @42
    @49
    notbid
    @22
    @42
    @70
    @22
    @46
    @42
    @70
    wo
    @48
    @4
    zeo
    syl
    ord
    sylbid
    imp
    @60
    peano2zm
    syl
    eqeltrrd
    #
    expclzd
    #
    @66
    @57
    c2
    @18
    cmul
    co
    @18
    @18
    caddc
    co
    ci
    @5
    cmul
    co
    #
    ci
    @6
    cmul
    co
    #
    cneg
    #
    caddc
    co
    #
    @8
    @57
    @18
    @72
    2timesd
    @57
    @18
    @73
    @18
    @75
    caddc
    @57
    @34
    @17
    cexp
    co
    #
    c1
    @3
    cdiv
    co
    #
    @5
    cmul
    co
    #
    @18
    @73
    @57
    @3
    c2
    @17
    cmul
    co
    #
    cexp
    co
    #
    @5
    @3
    cdiv
    co
    #
    @77
    @79
    @57
    @81
    @3
    @16
    cexp
    co
    @82
    @57
    @80
    @16
    @3
    cexp
    @57
    @16
    c2
    @57
    @52
    @68
    @16
    cc
    wcel
    @65
    ax-1cn
    @4
    c1
    subcl
    sylancl
    @58
    @66
    divcan2d
    #
    oveq2d
    @57
    @3
    @4
    @24
    @57
    @25
    a1i
    #
    @40
    @57
    @43
    a1i
    #
    @21
    @46
    @2
    @56
    @47
    ad2antlr
    #
    expm1d
    eqtrd
    @57
    @24
    @40
    @41
    @17
    cz
    wcel
    #
    @81
    @77
    wceq
    @84
    @85
    @41
    @57
    2z
    a1i
    #
    @71
    @3
    c2
    @17
    expmulz
    syl22anc
    @57
    @5
    @3
    @57
    @24
    @27
    @5
    cc
    wcel
    #
    @25
    @21
    @27
    @2
    @56
    @28
    ad2antlr
    #
    @3
    @4
    expcl
    sylancr
    #
    @84
    @85
    divrec2d
    3eqtr3d
    @34
    @15
    @17
    cexp
    @34
    @36
    @15
    @39
    i2
    eqtri
    oveq1i
    @78
    ci
    @5
    cmul
    c1
    ci
    cdiv
    co
    #
    cneg
    #
    @3
    cneg
    @78
    ci
    @92
    @3
    irec
    negeqi
    @68
    @38
    @51
    @93
    @78
    wceq
    ax-1cn
    ax-icn
    ine0
    c1
    ci
    divneg2
    mp3an
    ci
    ax-icn
    negnegi
    3eqtr3i
    oveq1i
    3eqtr3g
    @57
    @18
    @3
    @6
    cmul
    co
    #
    @75
    @57
    @36
    @17
    cexp
    co
    #
    @92
    @6
    cmul
    co
    #
    @18
    @94
    @57
    ci
    @80
    cexp
    co
    #
    @6
    ci
    cdiv
    co
    #
    @95
    @96
    @57
    @97
    ci
    @16
    cexp
    co
    @98
    @57
    @80
    @16
    ci
    cexp
    @83
    oveq2d
    @57
    ci
    @4
    @38
    @57
    ax-icn
    a1i
    #
    @51
    @57
    ine0
    a1i
    #
    @86
    expm1d
    eqtrd
    @57
    @38
    @51
    @41
    @87
    @97
    @95
    wceq
    @99
    @100
    @88
    @71
    ci
    c2
    @17
    expmulz
    syl22anc
    @57
    @6
    ci
    @57
    @38
    @27
    @6
    cc
    wcel
    #
    ax-icn
    @90
    ci
    @4
    expcl
    sylancr
    #
    @99
    @100
    divrec2d
    3eqtr3d
    @36
    @15
    @17
    cexp
    i2
    oveq1i
    @92
    @3
    @6
    cmul
    irec
    oveq1i
    3eqtr3g
    @57
    @38
    @101
    @94
    @75
    wceq
    ax-icn
    @102
    ci
    @6
    mulneg1
    sylancr
    eqtrd
    oveq12d
    @57
    @76
    @73
    @74
    cmin
    co
    @8
    @57
    @73
    @74
    @57
    @38
    @89
    @73
    cc
    wcel
    ax-icn
    @91
    ci
    @5
    mulcl
    sylancr
    @57
    @38
    @101
    @74
    cc
    wcel
    ax-icn
    @102
    ci
    @6
    mulcl
    sylancr
    negsubd
    @57
    ci
    @5
    @6
    @99
    @91
    @102
    subdid
    eqtr4d
    3eqtrd
    mvllmuld
    oveq1d
    ifeqda
    mpteq2dva
    syl5eq
    seqeq3d
    cA
    vn
    @13
    @13
    eqid
    atantayl
    eqbrtrd
end
