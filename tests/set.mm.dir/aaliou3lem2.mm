include "cn.mm"
include "wcel.mm"
include "cuz.mm"
include "cfv.mm"
include "wa.mm"
include "cc0.mm"
include "cioc.mm"
include "co.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "c2.mm"
include "cfa.mm"
include "cneg.mm"
include "cexp.mm"
include "crp.mm"
include "wceq.mm"
include "eluznn.mm"
include "cv.mm"
include "fveq2.mm"
include "negeqd.mm"
include "oveq2d.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "cz.mm"
include "2rp.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "faccl.mm"
include "nnzd.mm"
include "znegcld.mm"
include "rpexpcl.mm"
include "sylancr.mm"
include "eqeltrd.mm"
include "rpred.mm"
include "rpgt0d.mm"
include "wi.mm"
include "c1.mm"
include "caddc.mm"
include "breq12d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cdiv.mm"
include "cmin.mm"
include "cmul.mm"
include "nnnn0.mm"
include "leidd.mm"
include "nncn.mm"
include "subidd.mm"
include "cc.mm"
include "halfcn.mm"
include "exp0.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "rpcnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "nnz.mm"
include "uzid.mm"
include "oveq1.mm"
include "3syl.mm"
include "3brtr4d.mm"
include "a1i.mm"
include "rpge0d.mm"
include "simpl.mm"
include "halfre.mm"
include "halfgt0.mm"
include "elrpii.mm"
include "eluzelz.mm"
include "zsubcl.mm"
include "syl2anr.mm"
include "rpmulcld.mm"
include "jca31.mm"
include "adantr.mm"
include "adantl.mm"
include "zmulcld.mm"
include "simpr.mm"
include "nncnd.mm"
include "zcnd.mm"
include "mulneg1d.mm"
include "nnmulcld.mm"
include "nnge1d.mm"
include "wb.mm"
include "1re.mm"
include "nnred.mm"
include "leneg.mm"
include "mpbid.mm"
include "eqbrtrd.mm"
include "neg1z.mm"
include "eluz.mm"
include "sylancl.mm"
include "mpbird.mm"
include "2re.mm"
include "1le2.mm"
include "leexp2a.mm"
include "mp3an12.mm"
include "2cn.mm"
include "expn1.mm"
include "syl6breq.mm"
include "lemul12a.mm"
include "3impia.mm"
include "syl112anc.mm"
include "ex.mm"
include "facp1.mm"
include "ax-1cn.mm"
include "addcom.mm"
include "peano2cn.mm"
include "1cnd.mm"
include "adddid.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"
include "wne.mm"
include "2cnne0.mm"
include "expaddz.mm"
include "mpan.mm"
include "syl2anc.mm"
include "addsubd.mm"
include "uznn0sub.mm"
include "expp1.mm"
include "mulassd.mm"
include "eqtr4d.mm"
include "sylibrd.mm"
include "peano2nnd.mm"
include "peano2uz.mm"
include "3imtr4d.mm"
include "expcom.mm"
include "a2d.mm"
include "uzind4.mm"
include "impcom.mm"
include "cxr.mm"
include "w3a.mm"
include "0xr.mm"
include "aaliou3lem1.mm"
include "elioc2.mm"
include "mpbir3and.mm"

theorem aaliou3lem2
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let va: setvar a
  let vc: setvar c
  let vb: setvar b
  let vd: setvar d
  assume aaliou3lem.a: |- G = ( c e. ( ZZ>= ` A ) |-> ( ( 2 ^ -u ( ! ` A ) ) x. ( ( 1 / 2 ) ^ ( c - A ) ) ) )
  assume aaliou3lem.b: |- F = ( a e. NN |-> ( 2 ^ -u ( ! ` a ) ) )

  disjoint F c
  disjoint A a
  disjoint A c
  disjoint a c
  disjoint B a
  disjoint B c
  disjoint G a
  disjoint F b
  disjoint F d
  disjoint b c
  disjoint b d
  disjoint c d
  disjoint A b
  disjoint A d
  disjoint a b
  disjoint a d
  disjoint B b
  disjoint B d
  disjoint G b
  disjoint G d
  assert |- ( ( A e. NN /\ B e. ( ZZ>= ` A ) ) -> ( F ` B ) e. ( 0 (,] ( G ` B ) ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cA
    cuz
    cfv
    #
    wcel
    #
    wa
    #
    cB
    cF
    cfv
    #
    cc0
    cB
    cG
    cfv
    #
    cioc
    co
    wcel
    #
    @4
    cr
    wcel
    #
    cc0
    @4
    clt
    wbr
    #
    @4
    @5
    cle
    wbr
    #
    @3
    @4
    @3
    @4
    c2
    cB
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    crp
    @3
    cB
    cn
    wcel
    @4
    @12
    wceq
    cB
    cA
    eluznn
    #
    va
    cB
    c2
    va
    cv
    #
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    @12
    cn
    cF
    @14
    cB
    wceq
    #
    @16
    @11
    c2
    cexp
    @18
    @15
    @10
    @14
    cB
    cfa
    fveq2
    negeqd
    oveq2d
    aaliou3lem.b
    c2
    @11
    cexp
    ovex
    fvmpt
    syl
    @3
    c2
    crp
    wcel
    #
    @11
    cz
    wcel
    @12
    crp
    wcel
    2rp
    @3
    @10
    @3
    @10
    @3
    cB
    cn0
    wcel
    @10
    cn
    wcel
    @3
    cB
    @13
    nnnn0d
    cB
    faccl
    syl
    nnzd
    znegcld
    c2
    @11
    rpexpcl
    sylancr
    eqeltrd
    #
    rpred
    @3
    @4
    @20
    rpgt0d
    @2
    @0
    @9
    @0
    vb
    cv
    #
    cF
    cfv
    #
    @21
    cG
    cfv
    #
    cle
    wbr
    #
    wi
    @0
    cA
    cF
    cfv
    #
    cA
    cG
    cfv
    #
    cle
    wbr
    #
    wi
    #
    @0
    vd
    cv
    #
    cF
    cfv
    #
    @29
    cG
    cfv
    #
    cle
    wbr
    #
    wi
    @0
    @29
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @33
    cG
    cfv
    #
    cle
    wbr
    #
    wi
    @0
    @9
    wi
    vb
    vd
    cA
    cB
    @21
    cA
    wceq
    #
    @24
    @27
    @0
    @37
    @22
    @25
    @23
    @26
    cle
    @21
    cA
    cF
    fveq2
    @21
    cA
    cG
    fveq2
    breq12d
    imbi2d
    vb
    vd
    weq
    #
    @24
    @32
    @0
    @38
    @22
    @30
    @23
    @31
    cle
    @21
    @29
    cF
    fveq2
    @21
    @29
    cG
    fveq2
    breq12d
    imbi2d
    @21
    @33
    wceq
    #
    @24
    @36
    @0
    @39
    @22
    @34
    @23
    @35
    cle
    @21
    @33
    cF
    fveq2
    @21
    @33
    cG
    fveq2
    breq12d
    imbi2d
    @21
    cB
    wceq
    #
    @24
    @9
    @0
    @40
    @22
    @4
    @23
    @5
    cle
    @21
    cB
    cF
    fveq2
    @21
    cB
    cG
    fveq2
    breq12d
    imbi2d
    @28
    cA
    cz
    wcel
    #
    @0
    c2
    cA
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    @44
    c1
    c2
    cdiv
    co
    #
    cA
    cA
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    @25
    @26
    cle
    @0
    @44
    @44
    @48
    cle
    @0
    @44
    @0
    @44
    @0
    @19
    @43
    cz
    wcel
    #
    @44
    crp
    wcel
    #
    2rp
    @0
    @42
    @0
    @42
    @0
    cA
    cn0
    wcel
    #
    @42
    cn
    wcel
    #
    cA
    nnnn0
    cA
    faccl
    #
    syl
    nnzd
    znegcld
    c2
    @43
    rpexpcl
    #
    sylancr
    #
    rpred
    leidd
    @0
    @48
    @44
    c1
    cmul
    co
    @44
    @0
    @47
    c1
    @44
    cmul
    @0
    @47
    @45
    cc0
    cexp
    co
    #
    c1
    @0
    @46
    cc0
    @45
    cexp
    @0
    cA
    cA
    nncn
    #
    subidd
    oveq2d
    @45
    cc
    wcel
    #
    @56
    c1
    wceq
    halfcn
    @45
    exp0
    ax-mp
    syl6eq
    oveq2d
    @0
    @44
    @0
    @44
    @55
    rpcnd
    mulid1d
    eqtrd
    breqtrrd
    va
    cA
    @17
    @44
    cn
    cF
    @14
    cA
    wceq
    #
    @16
    @43
    c2
    cexp
    @59
    @15
    @42
    @14
    cA
    cfa
    fveq2
    negeqd
    oveq2d
    aaliou3lem.b
    c2
    @43
    cexp
    ovex
    fvmpt
    @0
    @41
    cA
    @1
    wcel
    @26
    @48
    wceq
    cA
    nnz
    #
    cA
    uzid
    vc
    cA
    @44
    @45
    vc
    cv
    #
    cA
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    @48
    @1
    cG
    @61
    cA
    wceq
    #
    @63
    @47
    @44
    cmul
    @65
    @62
    @46
    @45
    cexp
    @61
    cA
    cA
    cmin
    oveq1
    oveq2d
    oveq2d
    aaliou3lem.a
    @44
    @47
    cmul
    ovex
    fvmpt
    3syl
    3brtr4d
    a1i
    @29
    @1
    wcel
    #
    @0
    @32
    @36
    @0
    @66
    @32
    @36
    wi
    @0
    @66
    wa
    #
    c2
    @29
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    @44
    @45
    @29
    cA
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    c2
    @33
    cfa
    cfv
    #
    cneg
    #
    cexp
    co
    #
    @44
    @45
    @33
    cA
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    cle
    wbr
    #
    @32
    @36
    @67
    @74
    @70
    c2
    @69
    @29
    cmul
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    @73
    @45
    cmul
    co
    #
    cle
    wbr
    #
    @81
    @67
    @74
    @86
    @67
    @74
    wa
    @70
    cr
    wcel
    #
    cc0
    @70
    cle
    wbr
    #
    wa
    @73
    cr
    wcel
    #
    wa
    #
    @83
    cr
    wcel
    #
    cc0
    @83
    cle
    wbr
    #
    wa
    @45
    cr
    wcel
    #
    wa
    #
    @74
    @83
    @45
    cle
    wbr
    #
    @86
    @67
    @90
    @74
    @67
    @87
    @88
    @89
    @67
    @70
    @67
    @19
    @69
    cz
    wcel
    #
    @70
    crp
    wcel
    2rp
    @67
    @68
    @67
    @68
    @67
    @29
    cn0
    wcel
    #
    @68
    cn
    wcel
    @67
    @29
    @29
    cA
    eluznn
    #
    nnnn0d
    #
    @29
    faccl
    syl
    #
    nnzd
    znegcld
    #
    c2
    @69
    rpexpcl
    sylancr
    #
    rpred
    @67
    @70
    @102
    rpge0d
    @67
    @73
    @67
    @44
    @72
    @67
    @19
    @49
    @50
    2rp
    @67
    @42
    @67
    @42
    @67
    @51
    @52
    @67
    cA
    @0
    @66
    simpl
    nnnn0d
    @53
    syl
    nnzd
    znegcld
    @54
    sylancr
    #
    @67
    @45
    crp
    wcel
    @71
    cz
    wcel
    #
    @72
    crp
    wcel
    @45
    halfre
    halfgt0
    elrpii
    @66
    @29
    cz
    wcel
    #
    @41
    @104
    @0
    cA
    @29
    eluzelz
    #
    @60
    @29
    cA
    zsubcl
    syl2anr
    @45
    @71
    rpexpcl
    sylancr
    #
    rpmulcld
    rpred
    jca31
    adantr
    @67
    @94
    @74
    @67
    @91
    @92
    @93
    @67
    @83
    @67
    @19
    @82
    cz
    wcel
    #
    @83
    crp
    wcel
    2rp
    @67
    @69
    @29
    @101
    @66
    @105
    @0
    @106
    adantl
    #
    zmulcld
    #
    c2
    @82
    rpexpcl
    sylancr
    #
    rpred
    @67
    @83
    @111
    rpge0d
    @93
    @67
    halfre
    a1i
    jca31
    adantr
    @67
    @74
    simpr
    @67
    @95
    @74
    @67
    @83
    c2
    c1
    cneg
    #
    cexp
    co
    #
    @45
    cle
    @67
    @112
    @82
    cuz
    cfv
    wcel
    #
    @83
    @113
    cle
    wbr
    #
    @67
    @114
    @82
    @112
    cle
    wbr
    #
    @67
    @82
    @68
    @29
    cmul
    co
    #
    cneg
    #
    @112
    cle
    @67
    @68
    @29
    @67
    @68
    @100
    nncnd
    #
    @67
    @29
    @109
    zcnd
    #
    mulneg1d
    @67
    c1
    @117
    cle
    wbr
    #
    @118
    @112
    cle
    wbr
    #
    @67
    @117
    @67
    @68
    @29
    @100
    @98
    nnmulcld
    #
    nnge1d
    @67
    c1
    cr
    wcel
    @117
    cr
    wcel
    @121
    @122
    wb
    1re
    @67
    @117
    @123
    nnred
    c1
    @117
    leneg
    sylancr
    mpbid
    eqbrtrd
    @67
    @108
    @112
    cz
    wcel
    @114
    @116
    wb
    @110
    neg1z
    @82
    @112
    eluz
    sylancl
    mpbird
    c2
    cr
    wcel
    c1
    c2
    cle
    wbr
    @114
    @115
    2re
    1le2
    c2
    @82
    @112
    leexp2a
    mp3an12
    syl
    c2
    cc
    wcel
    #
    @113
    @45
    wceq
    2cn
    c2
    expn1
    ax-mp
    syl6breq
    adantr
    @90
    @94
    @74
    @95
    wa
    @86
    @70
    @73
    @83
    @45
    lemul12a
    3impia
    syl112anc
    ex
    @67
    @77
    @84
    @80
    @85
    cle
    @67
    @77
    c2
    @69
    @82
    caddc
    co
    #
    cexp
    co
    #
    @84
    @67
    @76
    @125
    c2
    cexp
    @67
    @76
    @68
    @33
    cmul
    co
    #
    cneg
    #
    @125
    @67
    @75
    @127
    @67
    @97
    @75
    @127
    wceq
    @99
    @29
    facp1
    syl
    negeqd
    @67
    @69
    @33
    cmul
    co
    @69
    c1
    @29
    caddc
    co
    #
    cmul
    co
    #
    @128
    @125
    @67
    @33
    @129
    @69
    cmul
    @67
    @29
    cc
    wcel
    #
    c1
    cc
    wcel
    @33
    @129
    wceq
    @120
    ax-1cn
    @29
    c1
    addcom
    sylancl
    oveq2d
    @67
    @68
    @33
    @119
    @67
    @131
    @33
    cc
    wcel
    @120
    @29
    peano2cn
    syl
    mulneg1d
    @67
    @130
    @69
    c1
    cmul
    co
    #
    @82
    caddc
    co
    @125
    @67
    @69
    c1
    @29
    @67
    @69
    @101
    zcnd
    #
    @67
    1cnd
    #
    @120
    adddid
    @67
    @132
    @69
    @82
    caddc
    @67
    @69
    @133
    mulid1d
    oveq1d
    eqtrd
    3eqtr3d
    eqtrd
    oveq2d
    @67
    @96
    @108
    @126
    @84
    wceq
    #
    @101
    @110
    @124
    c2
    cc0
    wne
    wa
    @96
    @108
    wa
    @135
    2cnne0
    c2
    @69
    @82
    expaddz
    mpan
    syl2anc
    eqtrd
    @67
    @80
    @44
    @72
    @45
    cmul
    co
    #
    cmul
    co
    @85
    @67
    @79
    @136
    @44
    cmul
    @67
    @79
    @45
    @71
    c1
    caddc
    co
    #
    cexp
    co
    #
    @136
    @67
    @78
    @137
    @45
    cexp
    @67
    @29
    c1
    cA
    @120
    @134
    @0
    cA
    cc
    wcel
    @66
    @57
    adantr
    addsubd
    oveq2d
    @67
    @58
    @71
    cn0
    wcel
    #
    @138
    @136
    wceq
    halfcn
    @66
    @139
    @0
    cA
    @29
    uznn0sub
    adantl
    @45
    @71
    expp1
    sylancr
    eqtrd
    oveq2d
    @67
    @44
    @72
    @45
    @67
    @44
    @103
    rpcnd
    @67
    @72
    @107
    rpcnd
    @58
    @67
    halfcn
    a1i
    mulassd
    eqtr4d
    breq12d
    sylibrd
    @67
    @30
    @70
    @31
    @73
    cle
    @67
    @29
    cn
    wcel
    @30
    @70
    wceq
    @98
    va
    @29
    @17
    @70
    cn
    cF
    va
    vd
    weq
    #
    @16
    @69
    c2
    cexp
    @140
    @15
    @68
    @14
    @29
    cfa
    fveq2
    negeqd
    oveq2d
    aaliou3lem.b
    c2
    @69
    cexp
    ovex
    fvmpt
    syl
    @66
    @31
    @73
    wceq
    @0
    vc
    @29
    @64
    @73
    @1
    cG
    vc
    vd
    weq
    #
    @63
    @72
    @44
    cmul
    @141
    @62
    @71
    @45
    cexp
    @61
    @29
    cA
    cmin
    oveq1
    oveq2d
    oveq2d
    aaliou3lem.a
    @44
    @72
    cmul
    ovex
    fvmpt
    adantl
    breq12d
    @67
    @34
    @77
    @35
    @80
    cle
    @67
    @33
    cn
    wcel
    @34
    @77
    wceq
    @67
    @29
    @98
    peano2nnd
    va
    @33
    @17
    @77
    cn
    cF
    @14
    @33
    wceq
    #
    @16
    @76
    c2
    cexp
    @142
    @15
    @75
    @14
    @33
    cfa
    fveq2
    negeqd
    oveq2d
    aaliou3lem.b
    c2
    @76
    cexp
    ovex
    fvmpt
    syl
    @66
    @35
    @80
    wceq
    #
    @0
    @66
    @33
    @1
    wcel
    @143
    cA
    @29
    peano2uz
    vc
    @33
    @64
    @80
    @1
    cG
    @61
    @33
    wceq
    #
    @63
    @79
    @44
    cmul
    @144
    @62
    @78
    @45
    cexp
    @61
    @33
    cA
    cmin
    oveq1
    oveq2d
    oveq2d
    aaliou3lem.a
    @44
    @79
    cmul
    ovex
    fvmpt
    syl
    adantl
    breq12d
    3imtr4d
    expcom
    a2d
    uzind4
    impcom
    @3
    cc0
    cxr
    wcel
    @5
    cr
    wcel
    @6
    @7
    @8
    @9
    w3a
    wb
    0xr
    cA
    cB
    cG
    vc
    aaliou3lem.a
    aaliou3lem1
    cc0
    @5
    @4
    elioc2
    sylancr
    mpbir3and
end
