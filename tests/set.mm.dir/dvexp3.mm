include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "cr.mm"
include "cneg.mm"
include "cn.mm"
include "wa.mm"
include "wo.mm"
include "cc.mm"
include "cc0.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cmpt.mm"
include "cdv.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "wceq.mm"
include "elznn0nn.mm"
include "cif.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "cfv.mm"
include "cvv.mm"
include "cpr.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "expcl.mm"
include "ancoms.mm"
include "c0ex.mm"
include "ovex.mm"
include "ifex.mm"
include "dvexp2.mm"
include "difssd.mm"
include "crest.mm"
include "ctop.mm"
include "eqid.mm"
include "cnfldtop.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "ccld.mm"
include "cha.mm"
include "cnfldhaus.mm"
include "0cn.mm"
include "sncld.mm"
include "mp2an.mm"
include "cldopn.mm"
include "dvmptres.mm"
include "ifid.mm"
include "id.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "wne.mm"
include "eldifsn.mm"
include "0z.mm"
include "peano2zm.mm"
include "expclz.mm"
include "mp3an3.mm"
include "sylbi.mm"
include "adantl.mm"
include "mul02d.mm"
include "sylan9eqr.mm"
include "ifeq1da.mm"
include "syl5eqr.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "cdiv.mm"
include "c2.mm"
include "eldifi.mm"
include "simpll.mm"
include "recnd.mm"
include "nnnn0.mm"
include "ad2antlr.mm"
include "expneg2.mm"
include "syl3anc.mm"
include "eldifsni.mm"
include "nnz.mm"
include "expclzd.mm"
include "expne0d.mm"
include "sylanbrc.mm"
include "simpr.mm"
include "sylib.mm"
include "reccl.mm"
include "syl.mm"
include "negex.mm"
include "expcld.mm"
include "dvexp.mm"
include "ax-1cn.mm"
include "dvrec.mm"
include "mp1i.mm"
include "oveq2.mm"
include "negeqd.mm"
include "dvmptco.mm"
include "2z.mm"
include "expmulz.mm"
include "syl22anc.mm"
include "eqcomd.mm"
include "mulneg1d.mm"
include "zmulcl.mm"
include "sylancl.mm"
include "reccld.mm"
include "mulcld.mm"
include "mul2negd.mm"
include "mul12d.mm"
include "expsubd.mm"
include "nncn.mm"
include "zcnd.mm"
include "sub32d.mm"
include "caddc.mm"
include "times2d.mm"
include "negsubd.mm"
include "eqtrd.mm"
include "nncand.mm"
include "oveq1d.mm"
include "divrec2d.mm"
include "3eqtr3rd.mm"
include "3eqtrd.mm"
include "jaoi.mm"

theorem dvexp3
  let vx: setvar x
  let cN: class N
  let vy: setvar y

  disjoint N x
  disjoint x y
  disjoint N y
  assert |- ( N e. ZZ -> ( CC _D ( x e. ( CC \ { 0 } ) |-> ( x ^ N ) ) ) = ( x e. ( CC \ { 0 } ) |-> ( N x. ( x ^ ( N - 1 ) ) ) ) )

  proof
    cN
    cz
    wcel
    cN
    cn0
    wcel
    #
    cN
    cr
    wcel
    #
    cN
    cneg
    #
    cn
    wcel
    #
    wa
    #
    wo
    cc
    vx
    cc
    cc0
    csn
    #
    cdif
    #
    vx
    cv
    #
    cN
    cexp
    co
    #
    cmpt
    #
    cdv
    co
    #
    vx
    @6
    cN
    @7
    cN
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmpt
    #
    wceq
    #
    cN
    elznn0nn
    @0
    @15
    @4
    @0
    @10
    vx
    @6
    cN
    cc0
    wceq
    #
    cc0
    @13
    cif
    #
    cmpt
    @14
    @0
    vx
    @8
    @17
    cc
    ccnfld
    ctopn
    cfv
    #
    @18
    cvv
    cc
    @6
    cc
    cr
    cc
    cpr
    wcel
    #
    @0
    cnelprrecn
    a1i
    @7
    cc
    wcel
    #
    @0
    @8
    cc
    wcel
    @7
    cN
    expcl
    ancoms
    @17
    cvv
    wcel
    @0
    @20
    wa
    @16
    cc0
    @13
    c0ex
    cN
    @12
    cmul
    ovex
    ifex
    a1i
    vx
    cN
    dvexp2
    @0
    cc
    @5
    difssd
    @18
    cc
    crest
    co
    #
    @18
    @18
    ctop
    wcel
    @21
    @18
    wceq
    @18
    @18
    eqid
    #
    cnfldtop
    @18
    ctop
    cc
    cc
    @18
    @18
    @22
    cnfldtopon
    toponunii
    #
    restid
    ax-mp
    eqcomi
    #
    @22
    @6
    @18
    wcel
    #
    @0
    @5
    @18
    ccld
    cfv
    wcel
    #
    @25
    @18
    cha
    wcel
    cc0
    cc
    wcel
    @26
    @18
    @22
    cnfldhaus
    0cn
    cc0
    @18
    cc
    @23
    sncld
    mp2an
    @5
    @18
    cc
    @23
    cldopn
    ax-mp
    #
    a1i
    dvmptres
    @0
    vx
    @6
    @13
    @17
    @0
    @7
    @6
    wcel
    #
    wa
    #
    @13
    @16
    @13
    @13
    cif
    @17
    @16
    @13
    ifid
    @29
    @16
    @13
    cc0
    @13
    @16
    @29
    @13
    cc0
    @7
    cc0
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    cc0
    @16
    cN
    cc0
    @12
    @31
    cmul
    @16
    id
    @16
    @11
    @30
    @7
    cexp
    cN
    cc0
    c1
    cmin
    oveq1
    oveq2d
    oveq12d
    @29
    @31
    @28
    @31
    cc
    wcel
    #
    @0
    @28
    @20
    @7
    cc0
    wne
    #
    wa
    @32
    @7
    cc
    cc0
    eldifsn
    @20
    @33
    @30
    cz
    wcel
    #
    @32
    cc0
    cz
    wcel
    @34
    0z
    cc0
    peano2zm
    ax-mp
    @7
    @30
    expclz
    mp3an3
    sylbi
    adantl
    mul02d
    sylan9eqr
    ifeq1da
    syl5eqr
    mpteq2dva
    eqtr4d
    @4
    @10
    cc
    vx
    @6
    c1
    @7
    @2
    cexp
    co
    #
    cdiv
    co
    #
    cmpt
    #
    cdv
    co
    vx
    @6
    c1
    @35
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cneg
    #
    @2
    @7
    @2
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cmul
    co
    #
    cmpt
    @14
    @4
    @9
    @37
    cc
    cdv
    @4
    vx
    @6
    @8
    @36
    @4
    @28
    wa
    #
    @20
    cN
    cc
    wcel
    @2
    cn0
    wcel
    #
    @8
    @36
    wceq
    @28
    @20
    @4
    @7
    cc
    @5
    eldifi
    adantl
    #
    @45
    cN
    @1
    @3
    @28
    simpll
    recnd
    #
    @3
    @46
    @1
    @28
    @2
    nnnn0
    #
    ad2antlr
    @7
    cN
    expneg2
    syl3anc
    mpteq2dva
    oveq2d
    @4
    vx
    vy
    @35
    @43
    c1
    vy
    cv
    #
    cdiv
    co
    #
    c1
    @50
    c2
    cexp
    co
    #
    cdiv
    co
    #
    cneg
    #
    cc
    cc
    @36
    @40
    cvv
    cvv
    @6
    @6
    @19
    @4
    cnelprrecn
    a1i
    #
    @55
    @45
    @35
    cc
    wcel
    @35
    cc0
    wne
    @35
    @6
    wcel
    @45
    @7
    @2
    @47
    @28
    @33
    @4
    @7
    cc
    cc0
    eldifsni
    adantl
    #
    @3
    @2
    cz
    wcel
    #
    @1
    @28
    @2
    nnz
    ad2antlr
    #
    expclzd
    @45
    @7
    @2
    @47
    @56
    @58
    expne0d
    @35
    cc
    cc0
    eldifsn
    sylanbrc
    @43
    cvv
    wcel
    #
    @45
    @2
    @42
    cmul
    ovex
    #
    a1i
    @4
    @50
    @6
    wcel
    #
    wa
    #
    @50
    cc
    wcel
    @50
    cc0
    wne
    wa
    #
    @51
    cc
    wcel
    @62
    @61
    @63
    @4
    @61
    simpr
    @50
    cc
    cc0
    eldifsn
    sylib
    @50
    reccl
    syl
    @54
    cvv
    wcel
    @62
    @53
    negex
    a1i
    @4
    vx
    @35
    @43
    cc
    @18
    @18
    cvv
    cc
    @6
    @55
    @4
    @20
    wa
    #
    @7
    @2
    @4
    @20
    simpr
    @3
    @46
    @1
    @20
    @49
    ad2antlr
    expcld
    @59
    @64
    @60
    a1i
    @3
    cc
    vx
    cc
    @35
    cmpt
    cdv
    co
    vx
    cc
    @43
    cmpt
    wceq
    @1
    vx
    @2
    dvexp
    adantl
    @4
    cc
    @5
    difssd
    @24
    @22
    @25
    @4
    @27
    a1i
    dvmptres
    c1
    cc
    wcel
    #
    cc
    vy
    @6
    @51
    cmpt
    cdv
    co
    vy
    @6
    @54
    cmpt
    wceq
    @4
    ax-1cn
    vy
    c1
    dvrec
    mp1i
    @50
    @35
    c1
    cdiv
    oveq2
    @50
    @35
    wceq
    #
    @53
    @39
    @66
    @52
    @38
    c1
    cdiv
    @50
    @35
    c2
    cexp
    oveq1
    oveq2d
    negeqd
    dvmptco
    @4
    vx
    @6
    @44
    @13
    @45
    @44
    c1
    @7
    @2
    c2
    cmul
    co
    #
    cexp
    co
    #
    cdiv
    co
    #
    cneg
    #
    cN
    @42
    cmul
    co
    #
    cneg
    #
    cmul
    co
    @69
    @71
    cmul
    co
    #
    @13
    @45
    @40
    @70
    @43
    @72
    cmul
    @45
    @39
    @69
    @45
    @38
    @68
    c1
    cdiv
    @45
    @68
    @38
    @45
    @20
    @33
    @57
    c2
    cz
    wcel
    #
    @68
    @38
    wceq
    @47
    @56
    @58
    @74
    @45
    2z
    a1i
    @7
    @2
    c2
    expmulz
    syl22anc
    eqcomd
    oveq2d
    negeqd
    @45
    cN
    @42
    @48
    @45
    @7
    @41
    @47
    @56
    @45
    @57
    @41
    cz
    wcel
    @58
    @2
    peano2zm
    syl
    #
    expclzd
    #
    mulneg1d
    oveq12d
    @45
    @69
    @71
    @45
    @68
    @45
    @7
    @67
    @47
    @56
    @45
    @57
    @74
    @67
    cz
    wcel
    @58
    2z
    @2
    c2
    zmulcl
    sylancl
    #
    expclzd
    #
    @45
    @7
    @67
    @47
    @56
    @77
    expne0d
    #
    reccld
    #
    @45
    cN
    @42
    @48
    @76
    mulcld
    mul2negd
    @45
    @73
    cN
    @69
    @42
    cmul
    co
    #
    cmul
    co
    @13
    @45
    @69
    cN
    @42
    @80
    @48
    @76
    mul12d
    @45
    @81
    @12
    cN
    cmul
    @45
    @7
    @41
    @67
    cmin
    co
    #
    cexp
    co
    @42
    @68
    cdiv
    co
    @12
    @81
    @45
    @7
    @41
    @67
    @47
    @56
    @77
    @75
    expsubd
    @45
    @82
    @11
    @7
    cexp
    @45
    @82
    @2
    @67
    cmin
    co
    #
    c1
    cmin
    co
    @11
    @45
    @2
    c1
    @67
    @3
    @2
    cc
    wcel
    @1
    @28
    @2
    nncn
    ad2antlr
    #
    @65
    @45
    ax-1cn
    a1i
    @45
    @67
    @77
    zcnd
    sub32d
    @45
    @83
    cN
    c1
    cmin
    @45
    @83
    @2
    @2
    cN
    cmin
    co
    #
    cmin
    co
    cN
    @45
    @67
    @85
    @2
    cmin
    @45
    @67
    @2
    @2
    caddc
    co
    @85
    @45
    @2
    @84
    times2d
    @45
    @2
    cN
    @84
    @48
    negsubd
    eqtrd
    oveq2d
    @45
    @2
    cN
    @84
    @48
    nncand
    eqtrd
    oveq1d
    eqtrd
    oveq2d
    @45
    @42
    @68
    @76
    @78
    @79
    divrec2d
    3eqtr3rd
    oveq2d
    eqtrd
    3eqtrd
    mpteq2dva
    3eqtrd
    jaoi
    sylbi
end
