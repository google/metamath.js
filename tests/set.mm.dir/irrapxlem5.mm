include "crp.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "cdiv.mm"
include "cfl.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "cif.mm"
include "clt.mm"
include "cn.mm"
include "wrex.mm"
include "cc0.mm"
include "cdenom.mm"
include "c2.mm"
include "cneg.mm"
include "cexp.mm"
include "w3a.mm"
include "cq.mm"
include "cr.mm"
include "cn0.mm"
include "simpr.mm"
include "rpreccld.mm"
include "rprege0d.mm"
include "flge0nn0.mm"
include "nn0p1nn.mm"
include "3syl.mm"
include "irrapxlem4.mm"
include "syldan.mm"
include "wne.mm"
include "simplrr.mm"
include "nnq.mm"
include "syl.mm"
include "simplrl.mm"
include "nnne0d.mm"
include "qdivcl.mm"
include "syl3anc.mm"
include "nnrpd.mm"
include "rpdivcld.mm"
include "rpgt0d.mm"
include "nnred.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "absidd.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "nncnd.mm"
include "qre.mm"
include "rpre.mm"
include "ad3antrrr.mm"
include "resubcld.mm"
include "recnd.mm"
include "absmuld.mm"
include "eqtr4d.mm"
include "cc.mm"
include "qcn.mm"
include "rpcn.mm"
include "subdid.mm"
include "divcan2d.mm"
include "mulcomd.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "remulcld.mm"
include "abssubd.mm"
include "3eqtrd.mm"
include "abscld.mm"
include "simpllr.mm"
include "rprecred.mm"
include "rpge0d.mm"
include "syl2anc.mm"
include "ifcld.mm"
include "rpred.mm"
include "fllep1.mm"
include "max2.mm"
include "letrd.mm"
include "lerecd.mm"
include "mpbid.mm"
include "rpne0d.mm"
include "recrecd.mm"
include "mulid2d.mm"
include "nnge1d.mm"
include "1red.mm"
include "lemul1d.mm"
include "eqbrtrd.mm"
include "ltletrd.mm"
include "wb.mm"
include "nngt0d.mm"
include "ltmul2.mm"
include "syl112anc.mm"
include "mpbird.mm"
include "msqgt0d.mm"
include "gt0ne0d.mm"
include "rereccld.mm"
include "qdencl.mm"
include "max1.mm"
include "divdiv1d.mm"
include "dividd.mm"
include "divrecd.mm"
include "3eqtr3rd.mm"
include "3brtr4d.mm"
include "cz.mm"
include "nnzd.mm"
include "divdenle.mm"
include "le2msq.mm"
include "syl22anc.mm"
include "lerec.mm"
include "wceq.mm"
include "2nn0.mm"
include "expneg.mm"
include "sylancl.mm"
include "sqvald.mm"
include "oveq2d.mm"
include "breqtrrd.mm"
include "breq2.mm"
include "oveq1.mm"
include "breq1d.mm"
include "fveq2.mm"
include "breq12d.mm"
include "3anbi123d.mm"
include "rspcev.mm"
include "syl13anc.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "mpd.mm"

theorem irrapxlem5
  let vx: setvar x
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint a x
  disjoint b x
  disjoint a b
  disjoint A a
  disjoint A b
  disjoint A y
  disjoint a y
  disjoint b y
  disjoint x y
  disjoint B a
  disjoint B b
  disjoint B y
  assert |- ( ( A e. RR+ /\ B e. RR+ ) -> E. x e. QQ ( 0 < x /\ ( abs ` ( x - A ) ) < B /\ ( abs ` ( x - A ) ) < ( ( denom ` x ) ^ -u 2 ) ) )

  proof
    cA
    crp
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cA
    va
    cv
    #
    cmul
    co
    #
    vb
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    c1
    @3
    c1
    cB
    cdiv
    co
    #
    cfl
    cfv
    #
    c1
    caddc
    co
    #
    cle
    wbr
    #
    @10
    @3
    cif
    #
    cdiv
    co
    #
    clt
    wbr
    #
    vb
    cn
    wrex
    va
    cn
    wrex
    #
    cc0
    vx
    cv
    #
    clt
    wbr
    #
    @16
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cB
    clt
    wbr
    #
    @19
    @16
    cdenom
    cfv
    #
    c2
    cneg
    #
    cexp
    co
    #
    clt
    wbr
    #
    w3a
    #
    vx
    cq
    wrex
    #
    @0
    @1
    @10
    cn
    wcel
    #
    @15
    @2
    @8
    cr
    wcel
    #
    cc0
    @8
    cle
    wbr
    #
    wa
    @9
    cn0
    wcel
    #
    @27
    @2
    @8
    @2
    cB
    @0
    @1
    simpr
    rpreccld
    rprege0d
    @8
    flge0nn0
    #
    @9
    nn0p1nn
    #
    3syl
    va
    vb
    cA
    @10
    irrapxlem4
    syldan
    @2
    @14
    @26
    va
    vb
    cn
    cn
    @2
    @3
    cn
    wcel
    #
    @5
    cn
    wcel
    #
    wa
    #
    wa
    #
    @14
    @26
    @36
    @14
    wa
    #
    @5
    @3
    cdiv
    co
    #
    cq
    wcel
    #
    cc0
    @38
    clt
    wbr
    #
    @38
    cA
    cmin
    co
    #
    cabs
    cfv
    #
    cB
    clt
    wbr
    #
    @42
    @38
    cdenom
    cfv
    #
    @22
    cexp
    co
    #
    clt
    wbr
    #
    @26
    @37
    @5
    cq
    wcel
    #
    @3
    cq
    wcel
    #
    @3
    cc0
    wne
    @39
    @37
    @34
    @47
    @2
    @33
    @34
    @14
    simplrr
    #
    @5
    nnq
    syl
    @37
    @33
    @48
    @2
    @33
    @34
    @14
    simplrl
    #
    @3
    nnq
    syl
    @37
    @3
    @50
    nnne0d
    #
    @5
    @3
    qdivcl
    syl3anc
    #
    @37
    @38
    @37
    @5
    @3
    @37
    @5
    @49
    nnrpd
    @37
    @3
    @50
    nnrpd
    #
    rpdivcld
    rpgt0d
    @37
    @43
    @3
    @42
    cmul
    co
    #
    @3
    cB
    cmul
    co
    #
    clt
    wbr
    #
    @37
    @54
    @7
    @55
    clt
    @37
    @54
    @3
    @41
    cmul
    co
    #
    cabs
    cfv
    #
    @5
    @4
    cmin
    co
    #
    cabs
    cfv
    @7
    @37
    @54
    @3
    cabs
    cfv
    #
    @42
    cmul
    co
    @58
    @37
    @3
    @60
    @42
    cmul
    @37
    @60
    @3
    @37
    @3
    @37
    @3
    @50
    nnred
    #
    @37
    @3
    @37
    @3
    @50
    nnnn0d
    nn0ge0d
    #
    absidd
    eqcomd
    oveq1d
    @37
    @3
    @41
    @37
    @3
    @50
    nncnd
    #
    @37
    @41
    @37
    @38
    cA
    @37
    @39
    @38
    cr
    wcel
    @52
    @38
    qre
    syl
    @0
    cA
    cr
    wcel
    @1
    @35
    @14
    cA
    rpre
    ad3antrrr
    #
    resubcld
    recnd
    #
    absmuld
    eqtr4d
    @37
    @57
    @59
    cabs
    @37
    @57
    @3
    @38
    cmul
    co
    #
    @3
    cA
    cmul
    co
    #
    cmin
    co
    @59
    @37
    @3
    @38
    cA
    @63
    @37
    @39
    @38
    cc
    wcel
    @52
    @38
    qcn
    syl
    @0
    cA
    cc
    wcel
    @1
    @35
    @14
    cA
    rpcn
    ad3antrrr
    #
    subdid
    @37
    @66
    @5
    @67
    @4
    cmin
    @37
    @5
    @3
    @37
    @5
    @49
    nncnd
    #
    @63
    @51
    divcan2d
    @37
    @3
    cA
    @63
    @68
    mulcomd
    oveq12d
    eqtrd
    fveq2d
    @37
    @5
    @4
    @69
    @37
    @4
    @37
    cA
    @3
    @64
    @61
    remulcld
    #
    recnd
    abssubd
    3eqtrd
    #
    @37
    @7
    @13
    @55
    @37
    @6
    @37
    @6
    @37
    @4
    @5
    @70
    @37
    @5
    @49
    nnred
    resubcld
    recnd
    abscld
    #
    @37
    @12
    @37
    @11
    @10
    @3
    crp
    @37
    @10
    @37
    @30
    @27
    @37
    @28
    @29
    @30
    @37
    cB
    @0
    @1
    @35
    @14
    simpllr
    #
    rprecred
    #
    @37
    @8
    @37
    cB
    @73
    rpreccld
    #
    rpge0d
    @31
    syl2anc
    @32
    syl
    #
    nnrpd
    @53
    ifcld
    #
    rprecred
    #
    @37
    @3
    cB
    @61
    @37
    cB
    @73
    rpred
    #
    remulcld
    #
    @36
    @14
    simpr
    #
    @37
    @13
    c1
    @8
    cdiv
    co
    #
    @55
    @78
    @37
    @8
    @75
    rprecred
    @80
    @37
    @8
    @12
    cle
    wbr
    @13
    @82
    cle
    wbr
    @37
    @8
    @10
    @12
    @74
    @37
    @10
    @76
    nnred
    #
    @37
    @11
    @10
    @3
    cr
    @83
    @61
    ifcld
    @37
    @28
    @8
    @10
    cle
    wbr
    @74
    @8
    fllep1
    syl
    @37
    @3
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    @10
    @12
    cle
    wbr
    @61
    @83
    @3
    @10
    max2
    syl2anc
    letrd
    @37
    @8
    @12
    @75
    @77
    lerecd
    mpbid
    @37
    @82
    c1
    cB
    cmul
    co
    #
    @55
    cle
    @37
    @82
    cB
    @86
    @37
    cB
    @37
    cB
    @79
    recnd
    #
    @37
    cB
    @73
    rpne0d
    recrecd
    @37
    cB
    @87
    mulid2d
    eqtr4d
    @37
    c1
    @3
    cle
    wbr
    @86
    @55
    cle
    wbr
    @37
    @3
    @50
    nnge1d
    @37
    c1
    @3
    cB
    @37
    1red
    @61
    @73
    lemul1d
    mpbid
    eqbrtrd
    letrd
    ltletrd
    eqbrtrd
    @37
    @42
    cr
    wcel
    #
    cB
    cr
    wcel
    @84
    cc0
    @3
    clt
    wbr
    #
    @43
    @56
    wb
    @37
    @41
    @65
    abscld
    #
    @79
    @61
    @37
    @3
    @50
    nngt0d
    #
    @42
    cB
    @3
    ltmul2
    syl112anc
    mpbird
    @37
    @42
    c1
    @44
    @44
    cmul
    co
    #
    cdiv
    co
    #
    @45
    clt
    @37
    @42
    c1
    @3
    @3
    cmul
    co
    #
    cdiv
    co
    #
    @93
    @90
    @37
    @94
    @37
    @3
    @3
    @61
    @61
    remulcld
    #
    @37
    @94
    @37
    @3
    @61
    @51
    msqgt0d
    #
    gt0ne0d
    #
    rereccld
    #
    @37
    @92
    @37
    @44
    @44
    @37
    @44
    @37
    @39
    @44
    cn
    wcel
    @52
    @38
    qdencl
    syl
    #
    nnred
    #
    @101
    remulcld
    #
    @37
    @92
    @37
    @44
    @101
    @37
    @44
    @100
    nnne0d
    msqgt0d
    #
    gt0ne0d
    rereccld
    @37
    @42
    @95
    clt
    wbr
    #
    @54
    @3
    @95
    cmul
    co
    #
    clt
    wbr
    #
    @37
    @7
    c1
    @3
    cdiv
    co
    #
    @54
    @105
    clt
    @37
    @7
    @13
    @107
    @72
    @78
    @37
    @3
    @61
    @51
    rereccld
    @81
    @37
    @3
    @12
    cle
    wbr
    #
    @13
    @107
    cle
    wbr
    @37
    @84
    @85
    @108
    @61
    @83
    @3
    @10
    max1
    syl2anc
    @37
    @3
    @12
    @53
    @77
    lerecd
    mpbid
    ltletrd
    @71
    @37
    @3
    @3
    cdiv
    co
    #
    @3
    cdiv
    co
    @3
    @94
    cdiv
    co
    @107
    @105
    @37
    @3
    @3
    @3
    @63
    @63
    @63
    @51
    @51
    divdiv1d
    @37
    @109
    c1
    @3
    cdiv
    @37
    @3
    @63
    @51
    dividd
    oveq1d
    @37
    @3
    @94
    @63
    @37
    @94
    @96
    recnd
    @98
    divrecd
    3eqtr3rd
    3brtr4d
    @37
    @88
    @95
    cr
    wcel
    @84
    @89
    @104
    @106
    wb
    @90
    @99
    @61
    @91
    @42
    @95
    @3
    ltmul2
    syl112anc
    mpbird
    @37
    @92
    @94
    cle
    wbr
    #
    @95
    @93
    cle
    wbr
    #
    @37
    @44
    @3
    cle
    wbr
    #
    @110
    @37
    @5
    cz
    wcel
    @33
    @112
    @37
    @5
    @49
    nnzd
    @50
    @5
    @3
    divdenle
    syl2anc
    @37
    @44
    cr
    wcel
    cc0
    @44
    cle
    wbr
    @84
    cc0
    @3
    cle
    wbr
    @112
    @110
    wb
    @101
    @37
    @44
    @37
    @44
    @100
    nnnn0d
    nn0ge0d
    @61
    @62
    @44
    @3
    le2msq
    syl22anc
    mpbid
    @37
    @92
    cr
    wcel
    cc0
    @92
    clt
    wbr
    @94
    cr
    wcel
    cc0
    @94
    clt
    wbr
    @110
    @111
    wb
    @102
    @103
    @96
    @97
    @92
    @94
    lerec
    syl22anc
    mpbid
    ltletrd
    @37
    @45
    c1
    @44
    c2
    cexp
    co
    #
    cdiv
    co
    #
    @93
    @37
    @44
    cc
    wcel
    c2
    cn0
    wcel
    @45
    @114
    wceq
    @37
    @44
    @100
    nncnd
    #
    2nn0
    @44
    c2
    expneg
    sylancl
    @37
    @113
    @92
    c1
    cdiv
    @37
    @44
    @115
    sqvald
    oveq2d
    eqtrd
    breqtrrd
    @25
    @40
    @43
    @46
    w3a
    vx
    @38
    cq
    @16
    @38
    wceq
    #
    @17
    @40
    @20
    @43
    @24
    @46
    @16
    @38
    cc0
    clt
    breq2
    @116
    @19
    @42
    cB
    clt
    @116
    @18
    @41
    cabs
    @16
    @38
    cA
    cmin
    oveq1
    fveq2d
    #
    breq1d
    @116
    @19
    @42
    @23
    @45
    clt
    @117
    @116
    @21
    @44
    @22
    cexp
    @16
    @38
    cdenom
    fveq2
    oveq1d
    breq12d
    3anbi123d
    rspcev
    syl13anc
    ex
    rexlimdvva
    mpd
end
