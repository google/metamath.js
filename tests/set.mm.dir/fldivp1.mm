include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cmin.mm"
include "cc0.mm"
include "cif.mm"
include "wceq.mm"
include "wne.mm"
include "wb.mm"
include "nnz.mm"
include "adantl.mm"
include "nnne0.mm"
include "peano2z.mm"
include "adantr.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "biimpa.mm"
include "flid.mm"
include "syl.mm"
include "cle.mm"
include "clt.mm"
include "cr.mm"
include "nnm1nn0.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "nnre.mm"
include "nngt0.mm"
include "divge0.mm"
include "syl22anc.mm"
include "ad2antlr.mm"
include "cmul.mm"
include "ltm1d.mm"
include "nncn.mm"
include "mulid1d.mm"
include "breqtrrd.mm"
include "1re.mm"
include "a1i.mm"
include "ltdivmul.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "nndivre.mm"
include "mpancom.mm"
include "flbi2.mm"
include "syl2anc.mm"
include "mpbir2and.mm"
include "eqtr4d.mm"
include "cc.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "ppncand.mm"
include "oveq1d.mm"
include "zcnd.mm"
include "subcl.mm"
include "sylancl.mm"
include "divdird.mm"
include "eqtr3d.mm"
include "dividd.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "zre.mm"
include "sylan.mm"
include "1z.mm"
include "fladdz.mm"
include "3eqtrrd.mm"
include "flcld.mm"
include "subaddd.mm"
include "iftrue.mm"
include "wn.mm"
include "cmo.mm"
include "cn0.mm"
include "zmodcl.mm"
include "resubcl.mm"
include "wo.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "id.mm"
include "dvdsval3.mm"
include "syl2anr.mm"
include "sylibrd.mm"
include "con1d.mm"
include "imp.mm"
include "jca.mm"
include "syl21anc.mm"
include "crp.mm"
include "nnrp.mm"
include "modlt.mm"
include "syl2an.mm"
include "lttrd.mm"
include "sylancom.mm"
include "modval.mm"
include "mulcld.mm"
include "sub32d.mm"
include "pncan.mm"
include "divsubdird.mm"
include "divcan3d.mm"
include "recnd.mm"
include "mpbid.mm"
include "subeq0ad.mm"
include "iffalse.mm"
include "pm2.61dan.mm"

theorem fldivp1
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. NN ) -> ( ( |_ ` ( ( M + 1 ) / N ) ) - ( |_ ` ( M / N ) ) ) = if ( N || ( M + 1 ) , 1 , 0 ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cN
    cM
    c1
    caddc
    co
    #
    cdvds
    wbr
    #
    @3
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cM
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cmin
    co
    #
    @4
    c1
    cc0
    cif
    #
    wceq
    @2
    @4
    wa
    #
    @9
    c1
    @10
    @11
    @9
    c1
    wceq
    #
    @8
    c1
    caddc
    co
    #
    @6
    wceq
    #
    @11
    @6
    @5
    cN
    c1
    cmin
    co
    #
    cN
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    @7
    c1
    caddc
    co
    #
    cfl
    cfv
    #
    @13
    @11
    @6
    @5
    @18
    @11
    @5
    cz
    wcel
    #
    @6
    @5
    wceq
    @2
    @4
    @21
    @2
    cN
    cz
    wcel
    #
    cN
    cc0
    wne
    #
    @3
    cz
    wcel
    #
    @4
    @21
    wb
    @1
    @22
    @0
    cN
    nnz
    adantl
    @1
    @23
    @0
    cN
    nnne0
    adantl
    #
    @0
    @24
    @1
    cM
    peano2z
    #
    adantr
    #
    cN
    @3
    dvdsval2
    syl3anc
    biimpa
    #
    @5
    flid
    syl
    @11
    @18
    @5
    wceq
    #
    cc0
    @16
    cle
    wbr
    #
    @16
    c1
    clt
    wbr
    #
    @1
    @30
    @0
    @4
    @1
    @15
    cr
    wcel
    #
    cc0
    @15
    cle
    wbr
    cN
    cr
    wcel
    #
    cc0
    cN
    clt
    wbr
    #
    @30
    @1
    @15
    cN
    nnm1nn0
    #
    nn0red
    #
    @1
    @15
    @35
    nn0ge0d
    cN
    nnre
    #
    cN
    nngt0
    #
    @15
    cN
    divge0
    syl22anc
    ad2antlr
    @1
    @31
    @0
    @4
    @1
    @31
    @15
    cN
    c1
    cmul
    co
    #
    clt
    wbr
    #
    @1
    @15
    cN
    @39
    clt
    @1
    cN
    @37
    ltm1d
    @1
    cN
    cN
    nncn
    #
    mulid1d
    breqtrrd
    @1
    @32
    c1
    cr
    wcel
    #
    @33
    @34
    @31
    @40
    wb
    @36
    @42
    @1
    1re
    a1i
    @37
    @38
    @15
    c1
    cN
    ltdivmul
    syl112anc
    mpbird
    ad2antlr
    @11
    @21
    @16
    cr
    wcel
    #
    @29
    @30
    @31
    wa
    wb
    @28
    @1
    @43
    @0
    @4
    @32
    @1
    @43
    @36
    @15
    cN
    nndivre
    mpancom
    ad2antlr
    @16
    @5
    flbi2
    syl2anc
    mpbir2and
    eqtr4d
    @2
    @18
    @20
    wceq
    @4
    @2
    @17
    @19
    cfl
    @2
    @17
    @7
    cN
    cN
    cdiv
    co
    #
    caddc
    co
    #
    @19
    @2
    cM
    cN
    caddc
    co
    #
    cN
    cdiv
    co
    #
    @17
    @45
    @2
    @3
    @15
    caddc
    co
    #
    cN
    cdiv
    co
    @47
    @17
    @2
    @48
    @46
    cN
    cdiv
    @2
    cM
    c1
    cN
    @0
    cM
    cc
    wcel
    #
    @1
    cM
    zcn
    adantr
    #
    c1
    cc
    wcel
    #
    @2
    ax-1cn
    a1i
    #
    @1
    cN
    cc
    wcel
    #
    @0
    @41
    adantl
    #
    ppncand
    oveq1d
    @2
    @3
    @15
    cN
    @2
    @3
    @27
    zcnd
    #
    @1
    @15
    cc
    wcel
    #
    @0
    @1
    @53
    @51
    @56
    @41
    ax-1cn
    cN
    c1
    subcl
    sylancl
    adantl
    @54
    @25
    divdird
    eqtr3d
    @2
    cM
    cN
    cN
    @50
    @54
    @54
    @25
    divdird
    eqtr3d
    @2
    @44
    c1
    @7
    caddc
    @2
    cN
    @54
    @25
    dividd
    oveq2d
    eqtrd
    fveq2d
    adantr
    @2
    @20
    @13
    wceq
    #
    @4
    @2
    @7
    cr
    wcel
    #
    c1
    cz
    wcel
    @57
    @0
    cM
    cr
    wcel
    @1
    @58
    cM
    zre
    cM
    cN
    nndivre
    sylan
    #
    1z
    @7
    c1
    fladdz
    sylancl
    adantr
    3eqtrrd
    @2
    @12
    @14
    wb
    @4
    @2
    @6
    @8
    c1
    @2
    @6
    @2
    @5
    @0
    @3
    cr
    wcel
    #
    @1
    @5
    cr
    wcel
    @0
    @24
    @60
    @26
    @3
    zre
    syl
    #
    @3
    cN
    nndivre
    sylan
    flcld
    #
    zcnd
    #
    @2
    @8
    @2
    @7
    @59
    flcld
    zcnd
    #
    @52
    subaddd
    adantr
    mpbird
    @4
    @10
    c1
    wceq
    @2
    @4
    c1
    cc0
    iftrue
    adantl
    eqtr4d
    @2
    @4
    wn
    #
    wa
    #
    @9
    cc0
    @10
    @66
    @9
    cc0
    wceq
    #
    @6
    @8
    wceq
    #
    @66
    @6
    @3
    cN
    cmo
    co
    #
    c1
    cmin
    co
    #
    cN
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    @6
    @8
    @66
    @73
    @6
    wceq
    #
    cc0
    @71
    cle
    wbr
    #
    @71
    c1
    clt
    wbr
    #
    @66
    @70
    cr
    wcel
    #
    cc0
    @70
    cle
    wbr
    @33
    @34
    wa
    #
    @75
    @2
    @77
    @65
    @2
    @69
    cr
    wcel
    @42
    @77
    @2
    @69
    @0
    @24
    @1
    @69
    cn0
    wcel
    #
    @26
    @3
    cN
    zmodcl
    sylan
    #
    nn0red
    #
    1re
    @69
    c1
    resubcl
    sylancl
    #
    adantr
    @66
    @70
    @66
    @69
    cn
    wcel
    #
    @70
    cn0
    wcel
    @2
    @65
    @83
    @2
    @83
    @4
    @2
    @83
    wn
    @69
    cc0
    wceq
    #
    @4
    @2
    @83
    @84
    @2
    @79
    @83
    @84
    wo
    @80
    @69
    elnn0
    sylib
    ord
    @1
    @1
    @24
    @4
    @84
    wb
    @0
    @1
    id
    @26
    cN
    @3
    dvdsval3
    syl2anr
    sylibrd
    con1d
    imp
    @69
    nnm1nn0
    syl
    nn0ge0d
    @1
    @78
    @0
    @65
    @1
    @33
    @34
    @37
    @38
    jca
    ad2antlr
    @70
    cN
    divge0
    syl21anc
    @2
    @76
    @65
    @2
    @76
    @70
    @39
    clt
    wbr
    #
    @2
    @70
    cN
    @39
    clt
    @2
    @70
    @69
    cN
    @82
    @81
    @1
    @33
    @0
    @37
    adantl
    #
    @2
    @69
    @81
    ltm1d
    @0
    @60
    cN
    crp
    wcel
    #
    @69
    cN
    clt
    wbr
    @1
    @61
    cN
    nnrp
    #
    @3
    cN
    modlt
    syl2an
    lttrd
    @2
    cN
    @54
    mulid1d
    breqtrrd
    @2
    @77
    @42
    @33
    @34
    @76
    @85
    wb
    @82
    @42
    @2
    1re
    a1i
    @86
    @1
    @34
    @0
    @38
    adantl
    @70
    c1
    cN
    ltdivmul
    syl112anc
    mpbird
    adantr
    @2
    @74
    @75
    @76
    wa
    wb
    #
    @65
    @2
    @6
    cz
    wcel
    @71
    cr
    wcel
    #
    @89
    @62
    @0
    @1
    @77
    @90
    @82
    @70
    cN
    nndivre
    sylancom
    #
    @71
    @6
    flbi2
    syl2anc
    adantr
    mpbir2and
    @66
    @72
    @7
    cfl
    @2
    @72
    @7
    wceq
    #
    @65
    @2
    @7
    @6
    cmin
    co
    #
    @71
    wceq
    @92
    @2
    @71
    cM
    cN
    @6
    cmul
    co
    #
    cmin
    co
    #
    cN
    cdiv
    co
    @7
    @94
    cN
    cdiv
    co
    #
    cmin
    co
    @93
    @2
    @70
    @95
    cN
    cdiv
    @2
    @70
    @3
    c1
    cmin
    co
    #
    @94
    cmin
    co
    #
    @95
    @2
    @70
    @3
    @94
    cmin
    co
    #
    c1
    cmin
    co
    @98
    @2
    @69
    @99
    c1
    cmin
    @0
    @60
    @87
    @69
    @99
    wceq
    @1
    @61
    @88
    @3
    cN
    modval
    syl2an
    oveq1d
    @2
    @3
    c1
    @94
    @55
    @52
    @2
    cN
    @6
    @54
    @63
    mulcld
    #
    sub32d
    eqtr4d
    @2
    @97
    cM
    @94
    cmin
    @2
    @49
    @51
    @97
    cM
    wceq
    @50
    ax-1cn
    cM
    c1
    pncan
    sylancl
    oveq1d
    eqtrd
    oveq1d
    @2
    cM
    @94
    cN
    @50
    @100
    @54
    @25
    divsubdird
    @2
    @96
    @6
    @7
    cmin
    @2
    @6
    cN
    @63
    @54
    @25
    divcan3d
    oveq2d
    3eqtrrd
    @2
    @7
    @6
    @71
    @2
    @7
    @59
    recnd
    @63
    @2
    @71
    @91
    recnd
    subaddd
    mpbid
    adantr
    fveq2d
    eqtr3d
    @2
    @67
    @68
    wb
    @65
    @2
    @6
    @8
    @63
    @64
    subeq0ad
    adantr
    mpbird
    @65
    @10
    cc0
    wceq
    @2
    @4
    c1
    cc0
    iffalse
    adantl
    eqtr4d
    pm2.61dan
end
