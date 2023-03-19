include "cr.mm"
include "wcel.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "cdiv.mm"
include "cv.mm"
include "cexp.mm"
include "cuz.mm"
include "cfv.mm"
include "wral.mm"
include "cn0.mm"
include "wrex.mm"
include "cn.mm"
include "2re.mm"
include "simp1.mm"
include "remulcl.mm"
include "sylancr.mm"
include "crp.mm"
include "simp3.mm"
include "wb.mm"
include "1re.mm"
include "simp2.mm"
include "difrp.mm"
include "mpbid.mm"
include "rerpdivcld.mm"
include "expnbnd.mm"
include "syl3anc.mm"
include "wa.mm"
include "2nn0.mm"
include "nnnn0.mm"
include "ad2antrl.mm"
include "nn0mulcl.mm"
include "cc0.mm"
include "cle.mm"
include "cif.mm"
include "ad2antrr.mm"
include "2nn.mm"
include "simprl.mm"
include "nnmulcl.mm"
include "eluznn.mm"
include "sylan.mm"
include "nnred.mm"
include "remulcld.mm"
include "0re.mm"
include "ifcl.mm"
include "sylancl.mm"
include "simplrl.mm"
include "resubcld.mm"
include "nnnn0d.mm"
include "reexpcl.mm"
include "syl2anc.mm"
include "nn0ge0d.mm"
include "max1.mm"
include "caddc.mm"
include "eluzle.mm"
include "adantl.mm"
include "leadd2dd.mm"
include "recnd.mm"
include "2timesd.mm"
include "breqtrrd.mm"
include "leaddsub.mm"
include "2cnd.mm"
include "subdid.mm"
include "max2.mm"
include "lemul12bd.mm"
include "mulcomd.mm"
include "mul32d.mm"
include "3brtr4d.mm"
include "rpred.mm"
include "simplrr.mm"
include "ltdivmuld.mm"
include "posdif.mm"
include "cz.mm"
include "nnzd.mm"
include "a1i.mm"
include "0lt1.mm"
include "lttrd.mm"
include "expgt0.mm"
include "mulgt0d.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "2t0e0.mm"
include "syl5eqr.mm"
include "ifboth.mm"
include "simpr.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "eluzsub.mm"
include "nngt0d.mm"
include "ltmul1.mm"
include "syl112anc.mm"
include "breqtrd.mm"
include "peano2re.mm"
include "syl.mm"
include "ltp1d.mm"
include "ltled.mm"
include "bernneq2.mm"
include "ltletrd.mm"
include "cc.mm"
include "wne.mm"
include "gt0ne0d.mm"
include "eluzelz.mm"
include "expsub.mm"
include "syl22anc.mm"
include "ltmuldiv.mm"
include "mpbird.mm"
include "lelttrd.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "raleqdv.mm"
include "rspcev.mm"
include "rexlimddv.mm"

theorem expmulnbnd
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n

  disjoint j k
  disjoint A j
  disjoint A k
  disjoint B j
  disjoint B k
  disjoint j n
  disjoint k n
  disjoint A n
  disjoint B n
  assert |- ( ( A e. RR /\ B e. RR /\ 1 < B ) -> E. j e. NN0 A. k e. ( ZZ>= ` j ) ( A x. k ) < ( B ^ k ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    c1
    cB
    clt
    wbr
    #
    w3a
    #
    c2
    cA
    cmul
    co
    #
    cB
    c1
    cmin
    co
    #
    cdiv
    co
    #
    cB
    vn
    cv
    #
    cexp
    co
    #
    clt
    wbr
    #
    cA
    vk
    cv
    #
    cmul
    co
    #
    cB
    @10
    cexp
    co
    #
    clt
    wbr
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cn0
    wrex
    #
    vn
    cn
    @3
    @6
    cr
    wcel
    @1
    @2
    @9
    vn
    cn
    wrex
    @3
    @4
    @5
    @3
    c2
    cr
    wcel
    #
    @0
    @4
    cr
    wcel
    #
    2re
    @0
    @1
    @2
    simp1
    #
    c2
    cA
    remulcl
    #
    sylancr
    @3
    @2
    @5
    crp
    wcel
    #
    @0
    @1
    @2
    simp3
    #
    @3
    c1
    cr
    wcel
    #
    @1
    @2
    @22
    wb
    1re
    @0
    @1
    @2
    simp2
    #
    c1
    cB
    difrp
    sylancr
    mpbid
    #
    rerpdivcld
    @25
    @23
    @6
    cB
    vn
    expnbnd
    syl3anc
    @3
    @7
    cn
    wcel
    #
    @9
    wa
    #
    wa
    #
    c2
    @7
    cmul
    co
    #
    cn0
    wcel
    #
    @13
    vk
    @30
    cuz
    cfv
    #
    wral
    #
    @17
    @29
    c2
    cn0
    wcel
    @7
    cn0
    wcel
    #
    @31
    2nn0
    @27
    @34
    @3
    @9
    @7
    nnnn0
    ad2antrl
    c2
    @7
    nn0mulcl
    sylancr
    @29
    @13
    vk
    @32
    @29
    @10
    @32
    wcel
    #
    wa
    #
    @11
    c2
    cc0
    cA
    cle
    wbr
    #
    cA
    cc0
    cif
    #
    cmul
    co
    #
    @10
    @7
    cmin
    co
    #
    cmul
    co
    #
    @12
    @36
    cA
    @10
    @3
    @0
    @28
    @35
    @20
    ad2antrr
    #
    @36
    @10
    @29
    @30
    cn
    wcel
    #
    @35
    @10
    cn
    wcel
    @29
    c2
    cn
    wcel
    @27
    @43
    2nn
    @3
    @27
    @9
    simprl
    c2
    @7
    nnmulcl
    sylancr
    @10
    @30
    eluznn
    sylan
    #
    nnred
    #
    remulcld
    @36
    @39
    @40
    @36
    @18
    @38
    cr
    wcel
    #
    @39
    cr
    wcel
    #
    2re
    @36
    @0
    cc0
    cr
    wcel
    #
    @46
    @42
    0re
    @37
    cA
    cc0
    cr
    ifcl
    sylancl
    #
    c2
    @38
    remulcl
    sylancr
    #
    @36
    @10
    @7
    @45
    @36
    @7
    @3
    @27
    @9
    @35
    simplrl
    #
    nnred
    #
    resubcld
    #
    remulcld
    #
    @36
    @1
    @10
    cn0
    wcel
    @12
    cr
    wcel
    #
    @3
    @1
    @28
    @35
    @25
    ad2antrr
    #
    @36
    @10
    @44
    nnnn0d
    #
    cB
    @10
    reexpcl
    syl2anc
    #
    @36
    @10
    cA
    cmul
    co
    c2
    @40
    cmul
    co
    #
    @38
    cmul
    co
    @11
    @41
    cle
    @36
    @10
    @59
    cA
    @38
    @45
    @36
    @18
    @40
    cr
    wcel
    #
    @59
    cr
    wcel
    2re
    @53
    c2
    @40
    remulcl
    sylancr
    @42
    @49
    @36
    @10
    @57
    nn0ge0d
    @36
    @48
    @0
    cc0
    @38
    cle
    wbr
    0re
    @42
    cc0
    cA
    max1
    sylancr
    @36
    @10
    c2
    @10
    cmul
    co
    #
    @30
    cmin
    co
    #
    @59
    cle
    @36
    @10
    @30
    caddc
    co
    #
    @61
    cle
    wbr
    #
    @10
    @62
    cle
    wbr
    #
    @36
    @63
    @10
    @10
    caddc
    co
    @61
    cle
    @36
    @30
    @10
    @10
    @36
    @18
    @7
    cr
    wcel
    @30
    cr
    wcel
    #
    2re
    @52
    c2
    @7
    remulcl
    sylancr
    #
    @45
    @45
    @35
    @30
    @10
    cle
    wbr
    @29
    @30
    @10
    eluzle
    adantl
    leadd2dd
    @36
    @10
    @36
    @10
    @45
    recnd
    #
    2timesd
    breqtrrd
    @36
    @10
    cr
    wcel
    #
    @66
    @61
    cr
    wcel
    #
    @64
    @65
    wb
    @45
    @67
    @36
    @18
    @69
    @70
    2re
    @45
    c2
    @10
    remulcl
    sylancr
    @10
    @30
    @61
    leaddsub
    syl3anc
    mpbid
    @36
    c2
    @10
    @7
    @36
    2cnd
    #
    @68
    @36
    @7
    @52
    recnd
    #
    subdid
    breqtrrd
    @36
    @48
    @0
    cA
    @38
    cle
    wbr
    0re
    @42
    cc0
    cA
    max2
    sylancr
    lemul12bd
    @36
    cA
    @10
    @36
    cA
    @42
    recnd
    @68
    mulcomd
    @36
    c2
    @38
    @40
    @71
    @36
    @38
    @49
    recnd
    @36
    @40
    @53
    recnd
    #
    mul32d
    3brtr4d
    @36
    @41
    @5
    @40
    cmul
    co
    #
    @8
    cmul
    co
    #
    @12
    @54
    @36
    @74
    @8
    @36
    @5
    @40
    @36
    @5
    @3
    @22
    @28
    @35
    @26
    ad2antrr
    #
    rpred
    #
    @53
    remulcld
    #
    @36
    @1
    @34
    @8
    cr
    wcel
    #
    @56
    @36
    @7
    @51
    nnnn0d
    cB
    @7
    reexpcl
    syl2anc
    #
    remulcld
    @58
    @36
    @41
    @5
    @8
    cmul
    co
    #
    @40
    cmul
    co
    #
    @75
    clt
    @36
    @39
    @81
    clt
    wbr
    #
    @41
    @82
    clt
    wbr
    #
    @36
    @4
    @81
    clt
    wbr
    #
    cc0
    @81
    clt
    wbr
    #
    @83
    @36
    @9
    @85
    @3
    @27
    @9
    @35
    simplrr
    @36
    @4
    @8
    @5
    @36
    @18
    @0
    @19
    2re
    @42
    @21
    sylancr
    @80
    @76
    ltdivmuld
    mpbid
    @36
    @5
    @8
    @77
    @80
    @36
    @2
    cc0
    @5
    clt
    wbr
    #
    @3
    @2
    @28
    @35
    @23
    ad2antrr
    #
    @36
    @24
    @1
    @2
    @87
    wb
    1re
    @56
    c1
    cB
    posdif
    sylancr
    mpbid
    @36
    @1
    @7
    cz
    wcel
    #
    cc0
    cB
    clt
    wbr
    cc0
    @8
    clt
    wbr
    #
    @56
    @36
    @7
    @51
    nnzd
    #
    @36
    cc0
    c1
    cB
    @48
    @36
    0re
    a1i
    #
    @24
    @36
    1re
    a1i
    @56
    cc0
    c1
    clt
    wbr
    @36
    0lt1
    a1i
    @88
    lttrd
    #
    cB
    @7
    expgt0
    syl3anc
    #
    mulgt0d
    @37
    @85
    @86
    @83
    cA
    cc0
    cA
    @38
    wceq
    @4
    @39
    @81
    clt
    cA
    @38
    c2
    cmul
    oveq2
    breq1d
    cc0
    @38
    wceq
    #
    cc0
    @39
    @81
    clt
    @95
    cc0
    c2
    cc0
    cmul
    co
    @39
    2t0e0
    cc0
    @38
    c2
    cmul
    oveq2
    syl5eqr
    breq1d
    ifboth
    syl2anc
    @36
    @47
    @81
    cr
    wcel
    @60
    cc0
    @40
    clt
    wbr
    @83
    @84
    wb
    @50
    @36
    @5
    @8
    @77
    @80
    remulcld
    @53
    @36
    @40
    @36
    @27
    @40
    @7
    cuz
    cfv
    wcel
    #
    @40
    cn
    wcel
    @51
    @36
    @89
    @89
    @10
    @7
    @7
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    @96
    @91
    @91
    @36
    @10
    @32
    @98
    @29
    @35
    simpr
    @36
    @30
    @97
    cuz
    @36
    @7
    @72
    2timesd
    fveq2d
    eleqtrd
    @7
    @7
    @10
    eluzsub
    syl3anc
    @40
    @7
    eluznn
    syl2anc
    #
    nngt0d
    @39
    @81
    @40
    ltmul1
    syl112anc
    mpbid
    @36
    @5
    @8
    @40
    @36
    @5
    @77
    recnd
    @36
    @8
    @80
    recnd
    @73
    mul32d
    breqtrd
    @36
    @75
    @12
    clt
    wbr
    #
    @74
    @12
    @8
    cdiv
    co
    #
    clt
    wbr
    #
    @36
    @74
    cB
    @40
    cexp
    co
    #
    @101
    clt
    @36
    @74
    @74
    c1
    caddc
    co
    #
    @103
    @78
    @36
    @74
    cr
    wcel
    #
    @104
    cr
    wcel
    @78
    @74
    peano2re
    syl
    @36
    @1
    @40
    cn0
    wcel
    #
    @103
    cr
    wcel
    @56
    @36
    @40
    @99
    nnnn0d
    #
    cB
    @40
    reexpcl
    syl2anc
    @36
    @74
    @78
    ltp1d
    @36
    @1
    @106
    cc0
    cB
    cle
    wbr
    @104
    @103
    cle
    wbr
    @56
    @107
    @36
    cc0
    cB
    @92
    @56
    @93
    ltled
    cB
    @40
    bernneq2
    syl3anc
    ltletrd
    @36
    cB
    cc
    wcel
    cB
    cc0
    wne
    @10
    cz
    wcel
    #
    @89
    @103
    @101
    wceq
    @36
    cB
    @56
    recnd
    @36
    cB
    @93
    gt0ne0d
    @35
    @108
    @29
    @30
    @10
    eluzelz
    adantl
    @91
    cB
    @10
    @7
    expsub
    syl22anc
    breqtrd
    @36
    @105
    @55
    @79
    @90
    @100
    @102
    wb
    @78
    @58
    @80
    @94
    @74
    @12
    @8
    ltmuldiv
    syl112anc
    mpbird
    lttrd
    lelttrd
    ralrimiva
    @16
    @33
    vj
    @30
    cn0
    @14
    @30
    wceq
    @13
    vk
    @15
    @32
    @14
    @30
    cuz
    fveq2
    raleqdv
    rspcev
    syl2anc
    rexlimddv
end
