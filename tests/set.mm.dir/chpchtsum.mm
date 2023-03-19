include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cicc.mm"
include "co.mm"
include "cprime.mm"
include "cin.mm"
include "cv.mm"
include "clog.mm"
include "cfv.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmul.mm"
include "csu.mm"
include "c1.mm"
include "cfz.mm"
include "cchp.mm"
include "ccxp.mm"
include "ccht.mm"
include "wa.mm"
include "chash.mm"
include "cfn.mm"
include "cc.mm"
include "wceq.mm"
include "fzfid.mm"
include "cn.mm"
include "inss2.mm"
include "simpr.mm"
include "sseldi.mm"
include "prmnn.mm"
include "syl.mm"
include "nnrpd.mm"
include "relogcld.mm"
include "recnd.mm"
include "fsumconst.mm"
include "syl2anc.mm"
include "cn0.mm"
include "cle.mm"
include "wbr.mm"
include "simpl.mm"
include "1red.mm"
include "nnred.mm"
include "c2.mm"
include "cuz.mm"
include "clt.mm"
include "prmuz2.mm"
include "eluz2b2.mm"
include "simprbi.mm"
include "w3a.mm"
include "inss1.mm"
include "wb.mm"
include "0re.mm"
include "elicc2.mm"
include "sylancr.mm"
include "mpbid.mm"
include "simp3d.mm"
include "ltletrd.mm"
include "rplogcld.mm"
include "rpdivcld.mm"
include "rpred.mm"
include "rpge0d.mm"
include "flge0nn0.mm"
include "hashfz1.mm"
include "oveq1d.mm"
include "flcld.mm"
include "zcnd.mm"
include "mulcomd.mm"
include "3eqtrrd.mm"
include "sumeq2dv.mm"
include "chpval2.mm"
include "0red.mm"
include "0lt1.mm"
include "a1i.mm"
include "elfzuz2.mm"
include "eluzle.mm"
include "adantl.mm"
include "cz.mm"
include "1z.mm"
include "flge.mm"
include "sylancl.mm"
include "mpbird.mm"
include "sylan2.mm"
include "ltled.mm"
include "elfznn.mm"
include "nnrecred.mm"
include "recxpcld.mm"
include "chtval.mm"
include "ppifi.mm"
include "wi.mm"
include "sseli.mm"
include "anim12i.mm"
include "wss.mm"
include "sselda.mm"
include "nngt0d.mm"
include "ex.mm"
include "adantrd.mm"
include "jcad.mm"
include "anim12ci.mm"
include "cexp.mm"
include "elin.mm"
include "simprll.mm"
include "biantrud.mm"
include "nnnn0d.mm"
include "nn0ge0d.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "baibd.mm"
include "syl22anc.mm"
include "bitr3d.mm"
include "syl5bb.mm"
include "simprr.mm"
include "elrpd.mm"
include "rerpdivcld.mm"
include "simprlr.mm"
include "nnzd.mm"
include "nnexpcld.mm"
include "logled.mm"
include "crp.mm"
include "relogexp.mm"
include "breq1d.mm"
include "lemuldivd.mm"
include "3bitrd.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "elfz5.mm"
include "3bitr4rd.mm"
include "anbi12d.mm"
include "bitr4d.mm"
include "cxpge0d.mm"
include "cxple2d.mm"
include "nncnd.mm"
include "cxpexp.mm"
include "nnne0d.mm"
include "recid2d.mm"
include "oveq2d.mm"
include "cxpmuld.mm"
include "cxp1d.mm"
include "3eqtr3d.mm"
include "breq12d.mm"
include "bernneq3.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "pm4.71rd.mm"
include "exp1d.mm"
include "nnge1d.mm"
include "leexp2ad.mm"
include "eqbrtrrd.mm"
include "3bitr2rd.mm"
include "bitrd.mm"
include "pm5.21ndd.mm"
include "adantrr.mm"
include "fsumcom2.mm"
include "eqtr4d.mm"
include "3eqtr4d.mm"

theorem chpchtsum
  let cA: class A
  let vk: setvar k
  let vd: setvar d
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x

  disjoint A k
  disjoint d k
  disjoint d m
  disjoint d n
  disjoint d p
  disjoint d x
  disjoint A d
  disjoint k m
  disjoint k n
  disjoint k p
  disjoint k x
  disjoint m n
  disjoint m p
  disjoint m x
  disjoint A m
  disjoint n p
  disjoint n x
  disjoint A n
  disjoint p x
  disjoint A p
  disjoint A x
  assert |- ( A e. RR -> ( psi ` A ) = sum_ k e. ( 1 ... ( |_ ` A ) ) ( theta ` ( A ^c ( 1 / k ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cicc
    co
    #
    cprime
    cin
    #
    vp
    cv
    #
    clog
    cfv
    #
    cA
    clog
    cfv
    #
    @4
    cdiv
    co
    #
    cfl
    cfv
    #
    cmul
    co
    #
    vp
    csu
    @2
    c1
    @7
    cfz
    co
    #
    @4
    vk
    csu
    #
    vp
    csu
    #
    cA
    cchp
    cfv
    c1
    cA
    cfl
    cfv
    #
    cfz
    co
    #
    cA
    c1
    vk
    cv
    #
    cdiv
    co
    #
    ccxp
    co
    #
    ccht
    cfv
    #
    vk
    csu
    #
    @0
    @2
    @8
    @10
    vp
    @0
    @3
    @2
    wcel
    #
    wa
    #
    @10
    @9
    chash
    cfv
    #
    @4
    cmul
    co
    #
    @7
    @4
    cmul
    co
    @8
    @20
    @9
    cfn
    wcel
    @4
    cc
    wcel
    #
    @10
    @22
    wceq
    @20
    c1
    @7
    fzfid
    #
    @20
    @4
    @20
    @3
    @20
    @3
    @20
    @3
    cprime
    wcel
    #
    @3
    cn
    wcel
    #
    @20
    @2
    cprime
    @3
    @1
    cprime
    inss2
    #
    @0
    @19
    simpr
    #
    sseldi
    #
    @3
    prmnn
    #
    syl
    #
    nnrpd
    relogcld
    recnd
    #
    @9
    @4
    vk
    fsumconst
    syl2anc
    @20
    @21
    @7
    @4
    cmul
    @20
    @7
    cn0
    wcel
    #
    @21
    @7
    wceq
    @20
    @6
    cr
    wcel
    #
    cc0
    @6
    cle
    wbr
    @33
    @20
    @6
    @20
    @5
    @4
    @20
    cA
    @0
    @19
    simpl
    #
    @20
    c1
    @3
    cA
    @20
    1red
    @20
    @3
    @31
    nnred
    #
    @35
    @20
    @3
    c2
    cuz
    cfv
    wcel
    #
    c1
    @3
    clt
    wbr
    #
    @20
    @25
    @37
    @29
    @3
    prmuz2
    #
    syl
    @37
    @26
    @38
    @3
    eluz2b2
    simprbi
    #
    syl
    #
    @20
    @3
    cr
    wcel
    #
    cc0
    @3
    cle
    wbr
    #
    @3
    cA
    cle
    wbr
    #
    @20
    @3
    @1
    wcel
    #
    @42
    @43
    @44
    w3a
    #
    @20
    @2
    @1
    @3
    @1
    cprime
    inss1
    @28
    sseldi
    @20
    cc0
    cr
    wcel
    #
    @0
    @45
    @46
    wb
    0re
    @35
    cc0
    cA
    @3
    elicc2
    #
    sylancr
    mpbid
    simp3d
    #
    ltletrd
    rplogcld
    @20
    @3
    @36
    @41
    rplogcld
    rpdivcld
    #
    rpred
    #
    @20
    @6
    @50
    rpge0d
    @6
    flge0nn0
    syl2anc
    @7
    hashfz1
    syl
    oveq1d
    @20
    @7
    @4
    @20
    @7
    @20
    @6
    @51
    flcld
    zcnd
    @32
    mulcomd
    3eqtrrd
    sumeq2dv
    cA
    vp
    chpval2
    @0
    @18
    @13
    cc0
    @16
    cicc
    co
    #
    cprime
    cin
    #
    @4
    vp
    csu
    #
    vk
    csu
    @11
    @0
    @13
    @17
    @54
    vk
    @0
    @14
    @13
    wcel
    #
    wa
    #
    @16
    cr
    wcel
    #
    @17
    @54
    wceq
    @56
    cA
    @15
    @0
    @55
    simpl
    #
    @56
    cc0
    cA
    @56
    0red
    #
    @58
    @56
    cc0
    c1
    cA
    @59
    @56
    1red
    @58
    cc0
    c1
    clt
    wbr
    @56
    0lt1
    a1i
    @55
    @0
    @12
    c1
    cuz
    cfv
    #
    wcel
    #
    c1
    cA
    cle
    wbr
    #
    @14
    c1
    @12
    elfzuz2
    @0
    @61
    wa
    #
    @62
    c1
    @12
    cle
    wbr
    #
    @61
    @64
    @0
    c1
    @12
    eluzle
    adantl
    @63
    @0
    c1
    cz
    wcel
    @62
    @64
    wb
    @0
    @61
    simpl
    1z
    cA
    c1
    flge
    sylancl
    mpbird
    sylan2
    ltletrd
    #
    ltled
    @56
    @14
    @55
    @14
    cn
    wcel
    #
    @0
    @14
    @12
    elfznn
    #
    adantl
    nnrecred
    recxpcld
    @16
    vp
    chtval
    syl
    sumeq2dv
    @0
    @2
    @9
    @13
    @53
    vp
    vk
    @4
    cA
    ppifi
    @0
    c1
    @12
    fzfid
    @24
    @0
    @25
    @66
    wa
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    @19
    @14
    @9
    wcel
    #
    wa
    #
    @55
    @3
    @53
    wcel
    #
    wa
    #
    @0
    @72
    @68
    @69
    @72
    @68
    wi
    @0
    @19
    @25
    @71
    @66
    @2
    cprime
    @3
    @27
    sseli
    @14
    @7
    elfznn
    anim12i
    a1i
    @0
    @19
    @69
    @71
    @0
    @19
    @69
    @20
    cc0
    @3
    cA
    @20
    0red
    @20
    @3
    @20
    @25
    @26
    @0
    @2
    cprime
    @3
    @2
    cprime
    wss
    @0
    @27
    a1i
    sselda
    @30
    syl
    #
    nnred
    @35
    @20
    @3
    @75
    nngt0d
    @49
    ltletrd
    ex
    adantrd
    jcad
    @0
    @74
    @68
    @69
    @74
    @68
    wi
    @0
    @55
    @66
    @73
    @25
    @67
    @53
    cprime
    @3
    @52
    cprime
    inss2
    sseli
    anim12ci
    a1i
    @0
    @55
    @69
    @73
    @0
    @55
    @69
    @65
    ex
    adantrd
    jcad
    @0
    @70
    @72
    @74
    wb
    @0
    @70
    wa
    #
    @72
    @44
    @3
    @14
    cexp
    co
    #
    cA
    cle
    wbr
    #
    wa
    #
    @74
    @76
    @19
    @44
    @71
    @78
    @19
    @45
    @25
    wa
    #
    @76
    @44
    @3
    @1
    cprime
    elin
    @76
    @45
    @80
    @44
    @76
    @25
    @45
    @0
    @25
    @66
    @69
    simprll
    #
    biantrud
    @76
    @47
    @0
    @42
    @43
    @45
    @44
    wb
    @76
    0red
    #
    @0
    @70
    simpl
    #
    @76
    @3
    @76
    @25
    @26
    @81
    @30
    syl
    #
    nnred
    #
    @76
    @3
    @76
    @3
    @84
    nnnn0d
    nn0ge0d
    #
    @47
    @0
    wa
    #
    @45
    @42
    @43
    wa
    #
    @44
    @87
    @45
    @46
    @88
    @44
    wa
    @48
    @42
    @43
    @44
    df-3an
    syl6bb
    baibd
    syl22anc
    bitr3d
    syl5bb
    @76
    @14
    @6
    cle
    wbr
    #
    @14
    @7
    cle
    wbr
    #
    @78
    @71
    @76
    @34
    @14
    cz
    wcel
    #
    @89
    @90
    wb
    @76
    @5
    @4
    @76
    cA
    @76
    cA
    @83
    @0
    @68
    @69
    simprr
    elrpd
    #
    relogcld
    #
    @76
    @3
    @85
    @76
    @37
    @38
    @76
    @25
    @37
    @81
    @39
    syl
    #
    @40
    syl
    rplogcld
    #
    rerpdivcld
    #
    @76
    @14
    @0
    @25
    @66
    @69
    simprlr
    #
    nnzd
    #
    @6
    @14
    flge
    syl2anc
    @76
    @78
    @77
    clog
    cfv
    #
    @5
    cle
    wbr
    @14
    @4
    cmul
    co
    #
    @5
    cle
    wbr
    @89
    @76
    @77
    cA
    @76
    @77
    @76
    @3
    @14
    @84
    @76
    @14
    @97
    nnnn0d
    #
    nnexpcld
    #
    nnrpd
    @92
    logled
    @76
    @99
    @100
    @5
    cle
    @76
    @3
    crp
    wcel
    @91
    @99
    @100
    wceq
    @76
    @3
    @84
    nnrpd
    @98
    @3
    @14
    relogexp
    syl2anc
    breq1d
    @76
    @14
    @5
    @4
    @76
    @14
    @97
    nnred
    #
    @93
    @95
    lemuldivd
    3bitrd
    @76
    @14
    @60
    wcel
    #
    @7
    cz
    wcel
    @71
    @90
    wb
    @76
    @14
    cn
    @60
    @97
    nnuz
    syl6eleq
    #
    @76
    @6
    @96
    flcld
    @14
    c1
    @7
    elfz5
    syl2anc
    3bitr4rd
    anbi12d
    @76
    @74
    @14
    cA
    cle
    wbr
    #
    @78
    wa
    @78
    @79
    @76
    @55
    @106
    @73
    @78
    @76
    @55
    @14
    @12
    cle
    wbr
    #
    @106
    @76
    @104
    @12
    cz
    wcel
    @55
    @107
    wb
    @105
    @76
    cA
    @83
    flcld
    @14
    c1
    @12
    elfz5
    syl2anc
    @76
    @0
    @91
    @106
    @107
    wb
    @83
    @98
    cA
    @14
    flge
    syl2anc
    bitr4d
    @73
    @3
    @52
    wcel
    #
    @25
    wa
    #
    @76
    @78
    @3
    @52
    cprime
    elin
    @76
    @109
    @3
    @16
    cle
    wbr
    #
    @3
    @14
    ccxp
    co
    #
    @16
    @14
    ccxp
    co
    #
    cle
    wbr
    @78
    @76
    @108
    @109
    @110
    @76
    @25
    @108
    @81
    biantrud
    @76
    @47
    @57
    @42
    @43
    @108
    @110
    wb
    @82
    @76
    cA
    @15
    @83
    @76
    cA
    @92
    rpge0d
    #
    @76
    @14
    @97
    nnrecred
    #
    recxpcld
    #
    @85
    @86
    @47
    @57
    wa
    #
    @108
    @88
    @110
    @116
    @108
    @42
    @43
    @110
    w3a
    @88
    @110
    wa
    cc0
    @16
    @3
    elicc2
    @42
    @43
    @110
    df-3an
    syl6bb
    baibd
    syl22anc
    bitr3d
    @76
    @3
    @16
    @14
    @85
    @86
    @115
    @76
    cA
    @15
    @83
    @113
    @114
    cxpge0d
    @76
    @14
    @97
    nnrpd
    cxple2d
    @76
    @111
    @77
    @112
    cA
    cle
    @76
    @3
    cc
    wcel
    @14
    cn0
    wcel
    #
    @111
    @77
    wceq
    @76
    @3
    @84
    nncnd
    #
    @101
    @3
    @14
    cxpexp
    syl2anc
    @76
    cA
    @15
    @14
    cmul
    co
    #
    ccxp
    co
    cA
    c1
    ccxp
    co
    @112
    cA
    @76
    @119
    c1
    cA
    ccxp
    @76
    @14
    @76
    @14
    @97
    nncnd
    #
    @76
    @14
    @97
    nnne0d
    recid2d
    oveq2d
    @76
    cA
    @15
    @14
    @92
    @114
    @120
    cxpmuld
    @76
    cA
    @76
    cA
    @83
    recnd
    cxp1d
    3eqtr3d
    breq12d
    3bitrd
    syl5bb
    anbi12d
    @76
    @78
    @106
    @76
    @14
    @77
    cle
    wbr
    #
    @78
    @106
    @76
    @14
    @77
    @103
    @76
    @77
    @102
    nnred
    #
    @76
    @37
    @117
    @14
    @77
    clt
    wbr
    @94
    @101
    @3
    @14
    bernneq3
    syl2anc
    ltled
    @76
    @14
    cr
    wcel
    @77
    cr
    wcel
    #
    @0
    @121
    @78
    wa
    @106
    wi
    @103
    @122
    @83
    @14
    @77
    cA
    letr
    syl3anc
    mpand
    pm4.71rd
    @76
    @78
    @44
    @76
    @3
    @77
    cle
    wbr
    #
    @78
    @44
    @76
    @3
    c1
    cexp
    co
    @3
    @77
    cle
    @76
    @3
    @118
    exp1d
    @76
    @3
    c1
    @14
    @85
    @76
    @3
    @84
    nnge1d
    @105
    leexp2ad
    eqbrtrrd
    @76
    @42
    @123
    @0
    @124
    @78
    wa
    @44
    wi
    @85
    @122
    @83
    @3
    @77
    cA
    letr
    syl3anc
    mpand
    pm4.71rd
    3bitr2rd
    bitrd
    ex
    pm5.21ndd
    @0
    @19
    @23
    @71
    @32
    adantrr
    fsumcom2
    eqtr4d
    3eqtr4d
end
