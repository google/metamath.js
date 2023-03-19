include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cmu.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "crab.mm"
include "csu.mm"
include "c1.mm"
include "cneg.mm"
include "cprime.mm"
include "chash.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cif.mm"
include "weq.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "breq1.mm"
include "anbi12d.mm"
include "elrab.mm"
include "muval2.mm"
include "adantrr.mm"
include "sylbi.mm"
include "adantl.mm"
include "sumeq2dv.mm"
include "wi.mm"
include "simpr.mm"
include "a1i.mm"
include "ss2rabdv.mm"
include "cz.mm"
include "ssrab2.mm"
include "sseldi.mm"
include "mucl.mm"
include "syl.mm"
include "zcnd.mm"
include "cdif.mm"
include "wn.mm"
include "difrab.mm"
include "pm3.21.mm"
include "necon1bd.mm"
include "imp.mm"
include "ss2rabi.mm"
include "eqsstri.mm"
include "sseli.mm"
include "eqeq1d.mm"
include "simprbi.mm"
include "cfz.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "fsumss.mm"
include "cpw.mm"
include "cmpt.mm"
include "oveq2d.mm"
include "cpc.mm"
include "eqid.mm"
include "oveq1.mm"
include "cbvmptv.mm"
include "oveq2.mm"
include "mpteq2dv.mm"
include "syl5eq.mm"
include "sqff1o.mm"
include "breq2.mm"
include "rabbidv.mm"
include "zex.mm"
include "prmz.mm"
include "ssriv.mm"
include "ssexi.mm"
include "rabex.mm"
include "fvmpt.mm"
include "cc.mm"
include "cn0.mm"
include "neg1cn.mm"
include "prmdvdsfi.mm"
include "elpwi.mm"
include "syl2an.mm"
include "hashcl.mm"
include "expcl.mm"
include "sylancr.mm"
include "fsumf1o.mm"
include "ciun.mm"
include "adantr.mm"
include "pwfi.mm"
include "sylib.mm"
include "sylancl.mm"
include "wral.mm"
include "wdisj.mm"
include "simprr.mm"
include "ralrimivva.mm"
include "invdisj.mm"
include "fsumiun.mm"
include "wrex.mm"
include "cle.mm"
include "cdom.mm"
include "ssdomg.mm"
include "sylc.mm"
include "wb.mm"
include "hashdom.mm"
include "mpbird.mm"
include "cuz.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "nn0zd.mm"
include "elfz5.mm"
include "eqidd.mm"
include "eqeq2.mm"
include "rspcev.mm"
include "ralrimiva.mm"
include "rabid2.mm"
include "sylibr.mm"
include "iunrab.mm"
include "syl6reqr.mm"
include "sumeq1d.mm"
include "cbc.mm"
include "cmul.mm"
include "elfznn0.mm"
include "fsumconst.mm"
include "elfzelz.mm"
include "hashbc.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "caddc.mm"
include "1pneg1e0.mm"
include "oveq1i.mm"
include "binom1p.mm"
include "syl5eqr.mm"
include "c0.mm"
include "nprmdvds1.mm"
include "breq2d.mm"
include "notbid.mm"
include "syl5ibr.mm"
include "ralrimiv.mm"
include "rabeq0.mm"
include "fveq2d.mm"
include "hash0.mm"
include "syl6eq.mm"
include "0exp0e1.mm"
include "c2.mm"
include "df-ne.mm"
include "eluz2b3.mm"
include "biimpri.mm"
include "sylan2br.mm"
include "exprmfct.mm"
include "rabn0.mm"
include "hashnncl.mm"
include "0expd.mm"
include "ifbothda.mm"
include "3eqtr2d.mm"
include "3eqtr3d.mm"
include "eqtr3d.mm"

theorem musum
  let vk: setvar k
  let vn: setvar n
  let cN: class N
  let vm: setvar m
  let cA: class A
  let vj: setvar j
  let cF: class F
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vz: setvar z
  let wph: wff ph
  let cB: class B
  let cC: class C

  disjoint k n
  disjoint N k
  disjoint N n
  disjoint k m
  disjoint A k
  disjoint A m
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint F j
  disjoint F k
  disjoint m n
  disjoint F m
  disjoint F n
  disjoint j p
  disjoint j q
  disjoint j s
  disjoint j x
  disjoint j z
  disjoint N j
  disjoint k p
  disjoint k q
  disjoint k s
  disjoint k x
  disjoint k z
  disjoint m p
  disjoint m q
  disjoint m s
  disjoint m x
  disjoint m z
  disjoint N m
  disjoint n p
  disjoint n q
  disjoint n s
  disjoint n x
  disjoint n z
  disjoint p q
  disjoint p s
  disjoint p x
  disjoint p z
  disjoint N p
  disjoint q s
  disjoint q x
  disjoint q z
  disjoint N q
  disjoint s x
  disjoint s z
  disjoint N s
  disjoint x z
  disjoint N x
  disjoint N z
  disjoint j ph
  disjoint k ph
  disjoint m ph
  disjoint B k
  disjoint C m
  assert |- ( N e. NN -> sum_ k e. { n e. NN | n || N } ( mmu ` k ) = if ( N = 1 , 1 , 0 ) )

  proof
    cN
    cn
    wcel
    #
    vn
    cv
    #
    cmu
    cfv
    #
    cc0
    wne
    #
    @1
    cN
    cdvds
    wbr
    #
    wa
    #
    vn
    cn
    crab
    #
    vk
    cv
    #
    cmu
    cfv
    #
    vk
    csu
    @6
    c1
    cneg
    #
    vp
    cv
    #
    @7
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    chash
    cfv
    #
    cexp
    co
    #
    vk
    csu
    #
    @4
    vn
    cn
    crab
    #
    @8
    vk
    csu
    cN
    c1
    wceq
    #
    c1
    cc0
    cif
    #
    @0
    @6
    @8
    @14
    vk
    @7
    @6
    wcel
    #
    @8
    @14
    wceq
    #
    @0
    @19
    @7
    cn
    wcel
    #
    @8
    cc0
    wne
    #
    @7
    cN
    cdvds
    wbr
    #
    wa
    #
    wa
    @20
    @5
    @24
    vn
    @7
    cn
    vn
    vk
    weq
    #
    @3
    @22
    @4
    @23
    @25
    @2
    @8
    cc0
    @1
    @7
    cmu
    fveq2
    #
    neeq1d
    @1
    @7
    cN
    cdvds
    breq1
    anbi12d
    elrab
    @21
    @22
    @20
    @23
    @7
    vp
    muval2
    adantrr
    sylbi
    adantl
    sumeq2dv
    @0
    @6
    @16
    @8
    vk
    @0
    @5
    @4
    vn
    cn
    @5
    @4
    wi
    @0
    @1
    cn
    wcel
    #
    wa
    @3
    @4
    simpr
    a1i
    ss2rabdv
    #
    @0
    @19
    wa
    #
    @8
    @29
    @21
    @8
    cz
    wcel
    @29
    @6
    cn
    @7
    @5
    vn
    cn
    ssrab2
    @0
    @19
    simpr
    sseldi
    @7
    mucl
    syl
    zcnd
    @7
    @16
    @6
    cdif
    #
    wcel
    #
    @8
    cc0
    wceq
    #
    @0
    @31
    @7
    @2
    cc0
    wceq
    #
    vn
    cn
    crab
    #
    wcel
    #
    @32
    @30
    @34
    @7
    @30
    @4
    @5
    wn
    #
    wa
    #
    vn
    cn
    crab
    @34
    @4
    @5
    vn
    cn
    difrab
    @37
    @33
    vn
    cn
    @37
    @33
    wi
    @27
    @4
    @36
    @33
    @4
    @5
    @2
    cc0
    @4
    @3
    pm3.21
    necon1bd
    imp
    a1i
    ss2rabi
    eqsstri
    sseli
    @35
    @21
    @32
    @33
    @32
    vn
    @7
    cn
    @25
    @2
    @8
    cc0
    @26
    eqeq1d
    elrab
    simprbi
    syl
    adantl
    @0
    c1
    cN
    cfz
    co
    #
    cfn
    wcel
    @16
    @38
    wss
    @16
    cfn
    wcel
    #
    @0
    c1
    cN
    fzfid
    cN
    vn
    dvdsssfz1
    @38
    @16
    ssfi
    syl2anc
    #
    fsumss
    @0
    @10
    cN
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    cpw
    #
    @9
    vx
    cv
    #
    chash
    cfv
    #
    cexp
    co
    #
    vx
    csu
    #
    @15
    @18
    @0
    @43
    @46
    @6
    @14
    vx
    vk
    vm
    @6
    @10
    vm
    cv
    #
    cdvds
    wbr
    #
    vp
    cprime
    crab
    #
    cmpt
    #
    @12
    @44
    @12
    wceq
    @45
    @13
    @9
    cexp
    @44
    @12
    chash
    fveq2
    oveq2d
    @0
    @39
    @6
    @16
    wss
    @6
    cfn
    wcel
    @40
    @28
    @16
    @6
    ssfi
    syl2anc
    vn
    @6
    vm
    @51
    vx
    cn
    vq
    cprime
    vq
    cv
    #
    @44
    cpc
    co
    #
    cmpt
    #
    cmpt
    cN
    vp
    @6
    eqid
    @51
    eqid
    #
    vx
    vm
    cn
    @54
    vp
    cprime
    @10
    @48
    cpc
    co
    #
    cmpt
    #
    vx
    vm
    weq
    #
    @54
    vp
    cprime
    @10
    @44
    cpc
    co
    #
    cmpt
    @57
    vq
    vp
    cprime
    @53
    @59
    @52
    @10
    @44
    cpc
    oveq1
    cbvmptv
    @58
    vp
    cprime
    @59
    @56
    @44
    @48
    @10
    cpc
    oveq2
    mpteq2dv
    syl5eq
    cbvmptv
    sqff1o
    @19
    @7
    @51
    cfv
    @12
    wceq
    @0
    vm
    @7
    @50
    @12
    @6
    @51
    vm
    vk
    weq
    @49
    @11
    vp
    cprime
    @48
    @7
    @10
    cdvds
    breq2
    rabbidv
    @55
    @11
    vp
    cprime
    cprime
    cz
    zex
    vp
    cprime
    cz
    @10
    prmz
    ssriv
    ssexi
    rabex
    fvmpt
    adantl
    @0
    @44
    @43
    wcel
    #
    wa
    #
    @9
    cc
    wcel
    #
    @45
    cn0
    wcel
    #
    @46
    cc
    wcel
    #
    neg1cn
    @61
    @44
    cfn
    wcel
    #
    @63
    @0
    @42
    cfn
    wcel
    #
    @44
    @42
    wss
    #
    @65
    @60
    cN
    vp
    prmdvdsfi
    #
    @44
    @42
    elpwi
    #
    @42
    @44
    ssfi
    #
    syl2an
    @44
    hashcl
    #
    syl
    @9
    @45
    expcl
    #
    sylancr
    fsumf1o
    @0
    vz
    cc0
    @42
    chash
    cfv
    #
    cfz
    co
    #
    vs
    cv
    #
    chash
    cfv
    #
    vz
    cv
    #
    wceq
    #
    vs
    @43
    crab
    #
    ciun
    #
    @46
    vx
    csu
    @74
    @79
    @46
    vx
    csu
    #
    vz
    csu
    #
    @47
    @18
    @0
    vz
    @74
    @79
    @46
    vx
    @0
    cc0
    @73
    fzfid
    @0
    @77
    @74
    wcel
    #
    wa
    #
    @43
    cfn
    wcel
    #
    @79
    @43
    wss
    @79
    cfn
    wcel
    #
    @84
    @66
    @85
    @0
    @66
    @83
    @68
    adantr
    @42
    pwfi
    sylib
    @78
    vs
    @43
    ssrab2
    #
    @43
    @79
    ssfi
    sylancl
    #
    @0
    @45
    @77
    wceq
    #
    vx
    @79
    wral
    vz
    @74
    wral
    vz
    @74
    @79
    wdisj
    @0
    @89
    vz
    vx
    @74
    @79
    @0
    @83
    @44
    @79
    wcel
    #
    wa
    #
    wa
    #
    @90
    @89
    @0
    @83
    @90
    simprr
    #
    @90
    @60
    @89
    @78
    @89
    vs
    @44
    @43
    vs
    vx
    weq
    @76
    @45
    @77
    @75
    @44
    chash
    fveq2
    eqeq1d
    elrab
    simprbi
    #
    syl
    ralrimivva
    vz
    vx
    @74
    @79
    @45
    invdisj
    syl
    @92
    @62
    @63
    @64
    neg1cn
    @92
    @65
    @63
    @92
    @66
    @67
    @65
    @0
    @66
    @91
    @68
    adantr
    @92
    @60
    @67
    @92
    @79
    @43
    @44
    @87
    @93
    sseldi
    @69
    syl
    @70
    syl2anc
    @71
    syl
    @72
    sylancr
    fsumiun
    @0
    @80
    @43
    @46
    vx
    @0
    @43
    @78
    vz
    @74
    wrex
    #
    vs
    @43
    crab
    #
    @80
    @0
    @95
    vs
    @43
    wral
    @43
    @96
    wceq
    @0
    @95
    vs
    @43
    @0
    @75
    @43
    wcel
    #
    wa
    #
    @76
    @74
    wcel
    #
    @76
    @76
    wceq
    #
    @95
    @98
    @99
    @76
    @73
    cle
    wbr
    #
    @98
    @101
    @75
    @42
    cdom
    wbr
    #
    @98
    @66
    @75
    @42
    wss
    #
    @102
    @0
    @66
    @97
    @68
    adantr
    #
    @97
    @103
    @0
    @75
    @42
    elpwi
    #
    adantl
    @75
    @42
    cfn
    ssdomg
    sylc
    @98
    @75
    cfn
    wcel
    #
    @66
    @101
    @102
    wb
    @0
    @66
    @103
    @106
    @97
    @68
    @105
    @42
    @75
    ssfi
    syl2an
    #
    @104
    @75
    @42
    cfn
    hashdom
    syl2anc
    mpbird
    @98
    @76
    cc0
    cuz
    cfv
    #
    wcel
    @73
    cz
    wcel
    @99
    @101
    wb
    @98
    @76
    cn0
    @108
    @98
    @106
    @76
    cn0
    wcel
    @107
    @75
    hashcl
    syl
    nn0uz
    syl6eleq
    @98
    @73
    @0
    @73
    cn0
    wcel
    #
    @97
    @0
    @66
    @109
    @68
    @42
    hashcl
    syl
    #
    adantr
    nn0zd
    @76
    cc0
    @73
    elfz5
    syl2anc
    mpbird
    @98
    @76
    eqidd
    @78
    @100
    vz
    @76
    @74
    @77
    @76
    @76
    eqeq2
    rspcev
    syl2anc
    ralrimiva
    @95
    vs
    @43
    rabid2
    sylibr
    @78
    vz
    vs
    @74
    @43
    iunrab
    syl6reqr
    sumeq1d
    @0
    @82
    @74
    @73
    @77
    cbc
    co
    #
    @9
    @77
    cexp
    co
    #
    cmul
    co
    #
    vz
    csu
    #
    cc0
    @73
    cexp
    co
    #
    @18
    @0
    @74
    @81
    @113
    vz
    @84
    @79
    @112
    vx
    csu
    #
    @79
    chash
    cfv
    #
    @112
    cmul
    co
    #
    @81
    @113
    @84
    @86
    @112
    cc
    wcel
    #
    @116
    @118
    wceq
    @88
    @84
    @62
    @77
    cn0
    wcel
    #
    @119
    neg1cn
    @83
    @120
    @0
    @77
    @73
    elfznn0
    adantl
    @9
    @77
    expcl
    sylancr
    @79
    @112
    vx
    fsumconst
    syl2anc
    @84
    @79
    @46
    @112
    vx
    @84
    @90
    wa
    @45
    @77
    @9
    cexp
    @90
    @89
    @84
    @94
    adantl
    oveq2d
    sumeq2dv
    @84
    @111
    @117
    @112
    cmul
    @0
    @66
    @77
    cz
    wcel
    @111
    @117
    wceq
    @83
    @68
    @77
    cc0
    @73
    elfzelz
    vs
    @42
    @77
    hashbc
    syl2an
    oveq1d
    3eqtr4d
    sumeq2dv
    @0
    @115
    c1
    @9
    caddc
    co
    #
    @73
    cexp
    co
    #
    @114
    @121
    cc0
    @73
    cexp
    1pneg1e0
    oveq1i
    @0
    @62
    @109
    @122
    @114
    wceq
    neg1cn
    @110
    @9
    vz
    @73
    binom1p
    sylancr
    syl5eqr
    @17
    @115
    c1
    wceq
    @115
    cc0
    wceq
    @115
    @18
    wceq
    @0
    c1
    cc0
    c1
    @18
    @115
    eqeq2
    cc0
    @18
    @115
    eqeq2
    @0
    @17
    wa
    #
    @115
    cc0
    cc0
    cexp
    co
    c1
    @123
    @73
    cc0
    cc0
    cexp
    @123
    @73
    c0
    chash
    cfv
    cc0
    @123
    @42
    c0
    chash
    @123
    @41
    wn
    #
    vp
    cprime
    wral
    @42
    c0
    wceq
    @123
    @124
    vp
    cprime
    @10
    cprime
    wcel
    @124
    @123
    @10
    c1
    cdvds
    wbr
    #
    wn
    @10
    nprmdvds1
    @123
    @41
    @125
    @123
    cN
    c1
    @10
    cdvds
    @0
    @17
    simpr
    breq2d
    notbid
    syl5ibr
    ralrimiv
    @41
    vp
    cprime
    rabeq0
    sylibr
    fveq2d
    hash0
    syl6eq
    oveq2d
    0exp0e1
    syl6eq
    @0
    @17
    wn
    #
    wa
    #
    @73
    @127
    @73
    cn
    wcel
    #
    @42
    c0
    wne
    #
    @127
    @41
    vp
    cprime
    wrex
    #
    @129
    @127
    cN
    c2
    cuz
    cfv
    wcel
    #
    @130
    @126
    @0
    cN
    c1
    wne
    #
    @131
    cN
    c1
    df-ne
    @131
    @0
    @132
    wa
    cN
    eluz2b3
    biimpri
    sylan2br
    cN
    vp
    exprmfct
    syl
    @41
    vp
    cprime
    rabn0
    sylibr
    @127
    @66
    @128
    @129
    wb
    @0
    @66
    @126
    @68
    adantr
    @42
    hashnncl
    syl
    mpbird
    0expd
    ifbothda
    3eqtr2d
    3eqtr3d
    eqtr3d
    3eqtr3d
end
