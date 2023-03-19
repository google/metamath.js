include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cn0.mm"
include "cprime.mm"
include "cfa.mm"
include "cpc.mm"
include "co.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "cexp.mm"
include "cdiv.mm"
include "cfl.mm"
include "csu.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wi.mm"
include "cc0.mm"
include "caddc.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "sumeq2sdv.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "imbi2d.mm"
include "cfn.mm"
include "fzfid.mm"
include "wss.mm"
include "sumz.mm"
include "olcs.mm"
include "syl.mm"
include "0nn0.mm"
include "a1i.mm"
include "elfznn.mm"
include "nnnn0d.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "adantl.mm"
include "simpll.mm"
include "pcfaclem.mm"
include "syl3anc.mm"
include "sumeq2dv.mm"
include "fac0.mm"
include "oveq2i.mm"
include "pc1.mm"
include "syl5eq.mm"
include "adantr.mm"
include "3eqtr4rd.mm"
include "ralrimiva.mm"
include "cz.mm"
include "nn0z.mm"
include "uzid.mm"
include "peano2uz.mm"
include "3syl.mm"
include "uzss.mm"
include "ssralv.mm"
include "cmul.mm"
include "facp1.mm"
include "wne.mm"
include "simplr.mm"
include "cn.mm"
include "faccl.mm"
include "nnz.mm"
include "nnne0.mm"
include "jca.mm"
include "nn0p1nn.mm"
include "pcmul.mm"
include "eqtr2d.mm"
include "cmin.mm"
include "cif.mm"
include "cdvds.mm"
include "wbr.mm"
include "nn0zd.mm"
include "prmnn.mm"
include "ad2antlr.mm"
include "nnexpcl.mm"
include "syl2an.mm"
include "fldivp1.mm"
include "syl2anc.mm"
include "cle.mm"
include "wb.mm"
include "elfzuz.mm"
include "pccld.mm"
include "elfz5.mm"
include "syl2anr.mm"
include "simpllr.mm"
include "nnzd.mm"
include "pcdvdsb.mm"
include "bitr2d.mm"
include "ifbid.mm"
include "eqtrd.mm"
include "cr.mm"
include "nn0red.mm"
include "peano2re.mm"
include "nndivred.mm"
include "flcld.mm"
include "zcnd.mm"
include "fsumsub.mm"
include "chash.mm"
include "fzfi.mm"
include "eluzelz.mm"
include "zred.mm"
include "clt.mm"
include "c2.mm"
include "prmuz2.mm"
include "bernneq3.mm"
include "wn.mm"
include "letrid.mm"
include "ord.mm"
include "nnexpcld.mm"
include "dvdsle.mm"
include "nnred.mm"
include "lenltd.mm"
include "sylibd.mm"
include "sylbid.mm"
include "syld.mm"
include "mt4d.mm"
include "eluzle.mm"
include "letrd.mm"
include "eluz.mm"
include "mpbird.mm"
include "fzss2.mm"
include "sumhash.mm"
include "sylancr.mm"
include "hashfz1.mm"
include "3eqtr3d.mm"
include "fsumcl.mm"
include "recnd.mm"
include "subaddd.mm"
include "mpbid.mm"
include "syl5ib.mm"
include "ralimdva.mm"
include "ex.mm"
include "a2d.mm"
include "nn0ind.mm"
include "imp.mm"
include "oveq2.mm"
include "sumeq1d.mm"
include "eqeq2d.mm"
include "rspcv.mm"
include "syl5.mm"
include "3impib.mm"
include "3com12.mm"

theorem pcfac
  let cP: class P
  let vk: setvar k
  let cM: class M
  let cN: class N
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cK: class K

  disjoint P k
  disjoint N k
  disjoint M k
  disjoint k m
  disjoint k n
  disjoint k x
  disjoint m n
  disjoint m x
  disjoint P m
  disjoint n x
  disjoint P n
  disjoint P x
  disjoint N m
  disjoint N x
  disjoint M m
  disjoint K k
  assert |- ( ( N e. NN0 /\ M e. ( ZZ>= ` N ) /\ P e. Prime ) -> ( P pCnt ( ! ` N ) ) = sum_ k e. ( 1 ... M ) ( |_ ` ( N / ( P ^ k ) ) ) )

  proof
    cM
    cN
    cuz
    cfv
    #
    wcel
    #
    cN
    cn0
    wcel
    #
    cP
    cprime
    wcel
    #
    cP
    cN
    cfa
    cfv
    #
    cpc
    co
    #
    c1
    cM
    cfz
    co
    #
    cN
    cP
    vk
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    vk
    csu
    #
    wceq
    #
    @1
    @2
    @3
    @12
    @2
    @3
    wa
    @5
    c1
    vm
    cv
    #
    cfz
    co
    #
    @10
    vk
    csu
    #
    wceq
    #
    vm
    @0
    wral
    #
    @1
    @12
    @2
    @3
    @17
    @3
    cP
    vx
    cv
    #
    cfa
    cfv
    #
    cpc
    co
    #
    @14
    @18
    @8
    cdiv
    co
    #
    cfl
    cfv
    #
    vk
    csu
    #
    wceq
    #
    vm
    @18
    cuz
    cfv
    #
    wral
    #
    wi
    @3
    cP
    cc0
    cfa
    cfv
    #
    cpc
    co
    #
    @14
    cc0
    @8
    cdiv
    co
    #
    cfl
    cfv
    #
    vk
    csu
    #
    wceq
    #
    vm
    cc0
    cuz
    cfv
    #
    wral
    #
    wi
    @3
    cP
    vn
    cv
    #
    cfa
    cfv
    #
    cpc
    co
    #
    @14
    @35
    @8
    cdiv
    co
    #
    cfl
    cfv
    #
    vk
    csu
    #
    wceq
    #
    vm
    @35
    cuz
    cfv
    #
    wral
    #
    wi
    @3
    cP
    @35
    c1
    caddc
    co
    #
    cfa
    cfv
    #
    cpc
    co
    #
    @14
    @44
    @8
    cdiv
    co
    #
    cfl
    cfv
    #
    vk
    csu
    #
    wceq
    #
    vm
    @44
    cuz
    cfv
    #
    wral
    #
    wi
    @3
    @17
    wi
    vx
    vn
    cN
    @18
    cc0
    wceq
    #
    @26
    @34
    @3
    @53
    @24
    @32
    vm
    @25
    @33
    @18
    cc0
    cuz
    fveq2
    @53
    @20
    @28
    @23
    @31
    @53
    @19
    @27
    cP
    cpc
    @18
    cc0
    cfa
    fveq2
    oveq2d
    @53
    @14
    @22
    @30
    vk
    @53
    @21
    @29
    cfl
    @18
    cc0
    @8
    cdiv
    oveq1
    fveq2d
    sumeq2sdv
    eqeq12d
    raleqbidv
    imbi2d
    @18
    @35
    wceq
    #
    @26
    @43
    @3
    @54
    @24
    @41
    vm
    @25
    @42
    @18
    @35
    cuz
    fveq2
    @54
    @20
    @37
    @23
    @40
    @54
    @19
    @36
    cP
    cpc
    @18
    @35
    cfa
    fveq2
    oveq2d
    @54
    @14
    @22
    @39
    vk
    @54
    @21
    @38
    cfl
    @18
    @35
    @8
    cdiv
    oveq1
    fveq2d
    sumeq2sdv
    eqeq12d
    raleqbidv
    imbi2d
    @18
    @44
    wceq
    #
    @26
    @52
    @3
    @55
    @24
    @50
    vm
    @25
    @51
    @18
    @44
    cuz
    fveq2
    @55
    @20
    @46
    @23
    @49
    @55
    @19
    @45
    cP
    cpc
    @18
    @44
    cfa
    fveq2
    oveq2d
    @55
    @14
    @22
    @48
    vk
    @55
    @21
    @47
    cfl
    @18
    @44
    @8
    cdiv
    oveq1
    fveq2d
    sumeq2sdv
    eqeq12d
    raleqbidv
    imbi2d
    @18
    cN
    wceq
    #
    @26
    @17
    @3
    @56
    @24
    @16
    vm
    @25
    @0
    @18
    cN
    cuz
    fveq2
    @56
    @20
    @5
    @23
    @15
    @56
    @19
    @4
    cP
    cpc
    @18
    cN
    cfa
    fveq2
    oveq2d
    @56
    @14
    @22
    @10
    vk
    @56
    @21
    @9
    cfl
    @18
    cN
    @8
    cdiv
    oveq1
    fveq2d
    sumeq2sdv
    eqeq12d
    raleqbidv
    imbi2d
    @3
    @32
    vm
    @33
    @3
    @13
    @33
    wcel
    #
    wa
    #
    @14
    cc0
    vk
    csu
    #
    cc0
    @31
    @28
    @58
    @14
    cfn
    wcel
    #
    @59
    cc0
    wceq
    #
    @58
    c1
    @13
    fzfid
    @14
    c1
    cuz
    cfv
    #
    wss
    @60
    @61
    @14
    vk
    c1
    sumz
    olcs
    syl
    @58
    @14
    @30
    cc0
    vk
    @58
    @7
    @14
    wcel
    #
    wa
    #
    cc0
    cn0
    wcel
    #
    @7
    @33
    wcel
    #
    @3
    @30
    cc0
    wceq
    @65
    @64
    0nn0
    a1i
    @63
    @66
    @58
    @63
    @7
    cn0
    @33
    @63
    @7
    @7
    @13
    elfznn
    nnnn0d
    #
    nn0uz
    syl6eleq
    adantl
    @3
    @57
    @63
    simpll
    cP
    @7
    cc0
    pcfaclem
    syl3anc
    sumeq2dv
    @3
    @28
    cc0
    wceq
    @57
    @3
    @28
    cP
    c1
    cpc
    co
    cc0
    @27
    c1
    cP
    cpc
    fac0
    oveq2i
    cP
    pc1
    syl5eq
    adantr
    3eqtr4rd
    ralrimiva
    @35
    cn0
    wcel
    #
    @3
    @43
    @52
    @68
    @3
    @43
    @52
    wi
    @68
    @3
    wa
    #
    @43
    @41
    vm
    @51
    wral
    #
    @52
    @69
    @44
    @42
    wcel
    #
    @51
    @42
    wss
    @43
    @70
    wi
    @69
    @35
    cz
    wcel
    #
    @35
    @42
    wcel
    @71
    @68
    @72
    @3
    @35
    nn0z
    adantr
    @35
    uzid
    @35
    @35
    peano2uz
    3syl
    @35
    @44
    uzss
    @41
    vm
    @51
    @42
    ssralv
    3syl
    @69
    @41
    @50
    vm
    @51
    @41
    @37
    cP
    @44
    cpc
    co
    #
    caddc
    co
    #
    @40
    @73
    caddc
    co
    #
    wceq
    @69
    @13
    @51
    wcel
    #
    wa
    #
    @50
    @37
    @40
    @73
    caddc
    oveq1
    @77
    @74
    @46
    @75
    @49
    @77
    @46
    cP
    @36
    @44
    cmul
    co
    #
    cpc
    co
    #
    @74
    @77
    @45
    @78
    cP
    cpc
    @77
    @68
    @45
    @78
    wceq
    @68
    @3
    @76
    simpll
    #
    @35
    facp1
    syl
    oveq2d
    @77
    @3
    @36
    cz
    wcel
    #
    @36
    cc0
    wne
    #
    wa
    #
    @44
    cz
    wcel
    #
    @44
    cc0
    wne
    #
    wa
    #
    @79
    @74
    wceq
    @68
    @3
    @76
    simplr
    #
    @77
    @68
    @36
    cn
    wcel
    #
    @83
    @80
    @35
    faccl
    @88
    @81
    @82
    @36
    nnz
    @36
    nnne0
    jca
    3syl
    @77
    @68
    @44
    cn
    wcel
    #
    @86
    @80
    @35
    nn0p1nn
    #
    @89
    @84
    @85
    @44
    nnz
    @44
    nnne0
    jca
    3syl
    @36
    @44
    cP
    pcmul
    syl3anc
    eqtr2d
    @77
    @49
    @40
    cmin
    co
    #
    @73
    wceq
    @75
    @49
    wceq
    @77
    @14
    @48
    @39
    cmin
    co
    #
    vk
    csu
    @14
    @7
    c1
    @73
    cfz
    co
    #
    wcel
    #
    c1
    cc0
    cif
    #
    vk
    csu
    #
    @91
    @73
    @77
    @14
    @92
    @95
    vk
    @77
    @63
    wa
    #
    @92
    @8
    @44
    cdvds
    wbr
    #
    c1
    cc0
    cif
    #
    @95
    @97
    @72
    @8
    cn
    wcel
    #
    @92
    @99
    wceq
    @97
    @35
    @77
    @68
    @63
    @80
    adantr
    #
    nn0zd
    @77
    cP
    cn
    wcel
    #
    @7
    cn0
    wcel
    #
    @100
    @63
    @3
    @102
    @68
    @76
    cP
    prmnn
    ad2antlr
    #
    @67
    cP
    @7
    nnexpcl
    syl2an
    #
    @35
    @8
    fldivp1
    syl2anc
    @97
    @98
    @94
    c1
    cc0
    @97
    @94
    @7
    @73
    cle
    wbr
    #
    @98
    @63
    @7
    @62
    wcel
    @73
    cz
    wcel
    #
    @94
    @106
    wb
    @77
    @7
    c1
    @13
    elfzuz
    @77
    @73
    @77
    cP
    @44
    @87
    @77
    @68
    @89
    @80
    @90
    syl
    #
    pccld
    #
    nn0zd
    #
    @7
    c1
    @73
    elfz5
    syl2anr
    @97
    @3
    @84
    @103
    @106
    @98
    wb
    @68
    @3
    @76
    @63
    simpllr
    @97
    @44
    @97
    @68
    @89
    @101
    @90
    syl
    nnzd
    @63
    @103
    @77
    @67
    adantl
    @7
    cP
    @44
    pcdvdsb
    syl3anc
    bitr2d
    ifbid
    eqtrd
    sumeq2dv
    @77
    @14
    @48
    @39
    vk
    @77
    c1
    @13
    fzfid
    #
    @97
    @48
    @97
    @47
    @97
    @44
    @8
    @77
    @44
    cr
    wcel
    #
    @63
    @77
    @35
    cr
    wcel
    #
    @112
    @77
    @35
    @80
    nn0red
    #
    @35
    peano2re
    syl
    #
    adantr
    @105
    nndivred
    flcld
    zcnd
    #
    @97
    @39
    @97
    @38
    @97
    @35
    @8
    @77
    @113
    @63
    @114
    adantr
    @105
    nndivred
    flcld
    zcnd
    #
    fsumsub
    @77
    @96
    @93
    chash
    cfv
    #
    @73
    @77
    @60
    @93
    @14
    wss
    #
    @96
    @118
    wceq
    c1
    @13
    fzfi
    @77
    @13
    @73
    cuz
    cfv
    wcel
    #
    @119
    @77
    @120
    @73
    @13
    cle
    wbr
    #
    @77
    @73
    @44
    @13
    @77
    @73
    @109
    nn0red
    #
    @115
    @77
    @13
    @76
    @13
    cz
    wcel
    #
    @69
    @44
    @13
    eluzelz
    adantl
    #
    zred
    @77
    @44
    cP
    @44
    cexp
    co
    #
    clt
    wbr
    #
    @73
    @44
    cle
    wbr
    #
    @77
    cP
    c2
    cuz
    cfv
    wcel
    #
    @44
    cn0
    wcel
    #
    @126
    @3
    @128
    @68
    @76
    cP
    prmuz2
    ad2antlr
    @77
    @44
    @108
    nnnn0d
    #
    cP
    @44
    bernneq3
    syl2anc
    @77
    @127
    wn
    @44
    @73
    cle
    wbr
    #
    @126
    wn
    #
    @77
    @127
    @131
    @77
    @73
    @44
    @122
    @115
    letrid
    ord
    @77
    @131
    @125
    @44
    cdvds
    wbr
    #
    @132
    @77
    @3
    @84
    @129
    @131
    @133
    wb
    @87
    @77
    @44
    @108
    nnzd
    @130
    @44
    cP
    @44
    pcdvdsb
    syl3anc
    @77
    @133
    @125
    @44
    cle
    wbr
    #
    @132
    @77
    @125
    cz
    wcel
    @89
    @133
    @134
    wi
    @77
    @125
    @77
    cP
    @44
    @104
    @130
    nnexpcld
    #
    nnzd
    @108
    @125
    @44
    dvdsle
    syl2anc
    @77
    @125
    @44
    @77
    @125
    @135
    nnred
    @115
    lenltd
    sylibd
    sylbid
    syld
    mt4d
    @76
    @44
    @13
    cle
    wbr
    @69
    @44
    @13
    eluzle
    adantl
    letrd
    @77
    @107
    @123
    @120
    @121
    wb
    @110
    @124
    @73
    @13
    eluz
    syl2anc
    mpbird
    @73
    c1
    @13
    fzss2
    syl
    @93
    @14
    vk
    sumhash
    sylancr
    @77
    @73
    cn0
    wcel
    @118
    @73
    wceq
    @109
    @73
    hashfz1
    syl
    eqtrd
    3eqtr3d
    @77
    @49
    @40
    @73
    @77
    @14
    @48
    vk
    @111
    @116
    fsumcl
    @77
    @14
    @39
    vk
    @111
    @117
    fsumcl
    @77
    @73
    @122
    recnd
    subaddd
    mpbid
    eqeq12d
    syl5ib
    ralimdva
    syld
    ex
    a2d
    nn0ind
    imp
    @16
    @12
    vm
    cM
    @0
    @13
    cM
    wceq
    #
    @15
    @11
    @5
    @136
    @14
    @6
    @10
    vk
    @13
    cM
    c1
    cfz
    oveq2
    sumeq1d
    eqeq2d
    rspcv
    syl5
    3impib
    3com12
end
