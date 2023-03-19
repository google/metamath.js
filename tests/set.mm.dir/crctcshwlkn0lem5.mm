include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "csn.mm"
include "cpr.mm"
include "wss.mm"
include "wif.mm"
include "cmin.mm"
include "cfzo.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wral.mm"
include "wi.mm"
include "cc.mm"
include "elfzoelz.mm"
include "zcnd.mm"
include "adantl.mm"
include "1cnd.mm"
include "adantr.mm"
include "elfzoel2.mm"
include "2addsubd.mm"
include "eqcomd.mm"
include "cn0.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "elfzo1.mm"
include "cuz.mm"
include "cz.mm"
include "cle.mm"
include "nnz.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "zaddcld.mm"
include "elfzo2.mm"
include "eluz2.mm"
include "cr.mm"
include "zre.mm"
include "nnre.mm"
include "anim12i.mm"
include "simplr.mm"
include "simpll.mm"
include "resubcld.mm"
include "lep1d.mm"
include "1red.mm"
include "readdcld.mm"
include "simpr.mm"
include "letr.mm"
include "syl3anc.mm"
include "mpand.mm"
include "lesubaddd.mm"
include "sylibd.mm"
include "ex.mm"
include "syl.mm"
include "3adant3.mm"
include "syl5com.mm"
include "com23.mm"
include "imp.mm"
include "3adant1.mm"
include "sylbi.mm"
include "com12.mm"
include "syl5bi.mm"
include "syl3anbrc.mm"
include "uznn0sub.mm"
include "simpl2.mm"
include "ax-1.mm"
include "imdistanri.mm"
include "lt2add.mm"
include "syl21anc.mm"
include "ltsubaddd.mm"
include "sylibrd.mm"
include "expcomd.mm"
include "3impia.mm"
include "com13.mm"
include "3adant2.mm"
include "impcom.mm"
include "3jca.mm"
include "sylanb.mm"
include "elfzo0.mm"
include "sylibr.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "sylan9eqr.mm"
include "eqeq12d.mm"
include "wb.mm"
include "sneqd.mm"
include "preq12d.mm"
include "sseq12d.mm"
include "ifpbi123d.mm"
include "rspcdv.mm"
include "mpdan.mm"
include "sylan.mm"
include "mpid.mm"
include "cfz.mm"
include "elfzofz.mm"
include "crctcshwlkn0lem3.mm"
include "sylan2.mm"
include "fzofzp1.mm"
include "ccsh.mm"
include "fveq1i.mm"
include "chash.mm"
include "cmo.mm"
include "cword.mm"
include "ltle.mm"
include "nnnn0.mm"
include "nn0sub.mm"
include "mpbid.mm"
include "1nn0.mm"
include "a1i.mm"
include "nn0addcld.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "fzoss1.mm"
include "3syl.mm"
include "sselda.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "cshwidxmod.mm"
include "eqcomi.mm"
include "crp.mm"
include "c2.mm"
include "cmul.mm"
include "eluzelre.mm"
include "nnrp.mm"
include "rpred.mm"
include "simpr3.mm"
include "simpl3.mm"
include "lt2addmuld.mm"
include "jca.mm"
include "jca31.mm"
include "2submod.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "mpbird.mm"
include "ralrimiva.mm"

theorem crctcshwlkn0lem5
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cP: class P
  let cQ: class Q
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let cF: class F
  let cH: class H
  let cI: class I
  let cN: class N
  let cJ: class J
  assume crctcshwlkn0lem.s: |- ( ph -> S e. ( 1 ..^ N ) )
  assume crctcshwlkn0lem.q: |- Q = ( x e. ( 0 ... N ) |-> if ( x <_ ( N - S ) , ( P ` ( x + S ) ) , ( P ` ( ( x + S ) - N ) ) ) )
  assume crctcshwlkn0lem.h: |- H = ( F cyclShift S )
  assume crctcshwlkn0lem.n: |- N = ( # ` F )
  assume crctcshwlkn0lem.f: |- ( ph -> F e. Word A )
  assume crctcshwlkn0lem.p: |- ( ph -> A. i e. ( 0 ..^ N ) if- ( ( P ` i ) = ( P ` ( i + 1 ) ) , ( I ` ( F ` i ) ) = { ( P ` i ) } , { ( P ` i ) , ( P ` ( i + 1 ) ) } C_ ( I ` ( F ` i ) ) ) )

  disjoint N x
  disjoint P x
  disjoint S x
  disjoint ph x
  disjoint F i
  disjoint I i
  disjoint N i
  disjoint P i
  disjoint S i
  disjoint i ph
  disjoint j ph
  disjoint i j
  disjoint j x
  disjoint J x
  assert |- ( ph -> A. j e. ( ( ( N - S ) + 1 ) ..^ N ) if- ( ( Q ` j ) = ( Q ` ( j + 1 ) ) , ( I ` ( H ` j ) ) = { ( Q ` j ) } , { ( Q ` j ) , ( Q ` ( j + 1 ) ) } C_ ( I ` ( H ` j ) ) ) )

  proof
    wph
    vj
    cv
    #
    cQ
    cfv
    #
    @0
    c1
    caddc
    co
    #
    cQ
    cfv
    #
    wceq
    #
    @0
    cH
    cfv
    #
    cI
    cfv
    #
    @1
    csn
    #
    wceq
    #
    @1
    @3
    cpr
    #
    @6
    wss
    #
    wif
    #
    vj
    cN
    cS
    cmin
    co
    #
    c1
    caddc
    co
    #
    cN
    cfzo
    co
    #
    wph
    @0
    @14
    wcel
    #
    wa
    #
    @11
    @0
    cS
    caddc
    co
    #
    cN
    cmin
    co
    #
    cP
    cfv
    #
    @2
    cS
    caddc
    co
    cN
    cmin
    co
    #
    cP
    cfv
    #
    wceq
    #
    @18
    cF
    cfv
    #
    cI
    cfv
    #
    @19
    csn
    #
    wceq
    #
    @19
    @21
    cpr
    #
    @24
    wss
    #
    wif
    #
    wph
    @15
    @29
    wph
    @15
    vi
    cv
    #
    cP
    cfv
    #
    @30
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wceq
    #
    @30
    cF
    cfv
    #
    cI
    cfv
    #
    @31
    csn
    #
    wceq
    #
    @31
    @33
    cpr
    #
    @36
    wss
    #
    wif
    #
    vi
    cc0
    cN
    cfzo
    co
    #
    wral
    #
    @29
    crctcshwlkn0lem.p
    wph
    @15
    @43
    @29
    wi
    #
    wph
    cS
    c1
    cN
    cfzo
    co
    wcel
    #
    @15
    @44
    crctcshwlkn0lem.s
    @45
    @15
    wa
    #
    @18
    c1
    caddc
    co
    #
    @20
    wceq
    #
    @44
    @46
    @20
    @47
    @46
    @0
    c1
    cS
    cN
    @15
    @0
    cc
    wcel
    @45
    @15
    @0
    @0
    @13
    cN
    elfzoelz
    #
    zcnd
    adantl
    @46
    1cnd
    @45
    cS
    cc
    wcel
    @15
    @45
    cS
    cS
    c1
    cN
    elfzoelz
    #
    zcnd
    adantr
    @45
    cN
    cc
    wcel
    @15
    @45
    cN
    cS
    c1
    cN
    elfzoel2
    zcnd
    adantr
    2addsubd
    eqcomd
    @46
    @48
    wa
    #
    @41
    @29
    vi
    @18
    @42
    @46
    @18
    @42
    wcel
    #
    @48
    @46
    @18
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    @18
    cN
    clt
    wbr
    #
    w3a
    #
    @52
    @45
    cS
    cn
    wcel
    #
    @54
    cS
    cN
    clt
    wbr
    #
    w3a
    #
    @15
    @56
    cN
    cS
    elfzo1
    #
    @59
    @15
    wa
    #
    @53
    @54
    @55
    @61
    @17
    cN
    cuz
    cfv
    wcel
    #
    @53
    @61
    cN
    cz
    wcel
    #
    @17
    cz
    wcel
    cN
    @17
    cle
    wbr
    #
    @62
    @59
    @63
    @15
    @54
    @57
    @63
    @58
    cN
    nnz
    3ad2ant2
    adantr
    @61
    @0
    cS
    @15
    @0
    cz
    wcel
    #
    @59
    @49
    adantl
    @59
    cS
    cz
    wcel
    #
    @15
    @57
    @54
    @66
    @58
    cS
    nnz
    3ad2ant1
    adantr
    zaddcld
    @59
    @15
    @64
    @15
    @0
    @13
    cuz
    cfv
    wcel
    #
    @63
    @0
    cN
    clt
    wbr
    #
    w3a
    #
    @59
    @64
    @0
    @13
    cN
    elfzo2
    #
    @69
    @59
    @64
    @67
    @63
    @59
    @64
    wi
    #
    @68
    @67
    @13
    cz
    wcel
    #
    @65
    @13
    @0
    cle
    wbr
    #
    w3a
    #
    @71
    @13
    @0
    eluz2
    #
    @65
    @73
    @71
    @72
    @65
    @73
    @71
    @65
    @59
    @73
    @64
    @65
    @0
    cr
    wcel
    #
    @59
    @73
    @64
    wi
    #
    @0
    zre
    #
    @57
    @54
    @76
    @77
    wi
    #
    @58
    @57
    @54
    wa
    #
    cS
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    wa
    #
    @79
    @57
    @81
    @54
    @82
    cS
    nnre
    #
    cN
    nnre
    anim12i
    #
    @83
    @76
    @77
    @83
    @76
    wa
    #
    @73
    @12
    @0
    cle
    wbr
    #
    @64
    @86
    @12
    @13
    cle
    wbr
    #
    @73
    @87
    @86
    @12
    @86
    cN
    cS
    @81
    @82
    @76
    simplr
    #
    @81
    @82
    @76
    simpll
    #
    resubcld
    #
    lep1d
    @86
    @12
    cr
    wcel
    @13
    cr
    wcel
    @76
    @88
    @73
    wa
    @87
    wi
    @91
    @86
    @12
    c1
    @91
    @86
    1red
    readdcld
    @83
    @76
    simpr
    #
    @12
    @13
    @0
    letr
    syl3anc
    mpand
    @86
    cN
    cS
    @0
    @89
    @90
    @92
    lesubaddd
    sylibd
    ex
    syl
    3adant3
    syl5com
    com23
    imp
    3adant1
    sylbi
    3ad2ant1
    #
    com12
    syl5bi
    imp
    cN
    @17
    eluz2
    syl3anbrc
    cN
    @17
    uznn0sub
    syl
    @57
    @54
    @58
    @15
    simpl2
    @15
    @59
    @55
    @15
    @69
    @59
    @55
    wi
    #
    @70
    @67
    @68
    @94
    @63
    @67
    @68
    @94
    @67
    @74
    @68
    @94
    wi
    #
    @75
    @65
    @72
    @95
    @73
    @59
    @68
    @65
    @55
    @57
    @54
    @58
    @68
    @65
    @55
    wi
    #
    wi
    #
    @80
    @83
    @58
    @97
    wi
    @85
    @83
    @68
    @58
    @96
    @83
    @65
    @68
    @58
    wa
    #
    @55
    @83
    @65
    @98
    @55
    wi
    @83
    @65
    wa
    #
    @98
    @17
    cN
    cN
    caddc
    co
    clt
    wbr
    #
    @55
    @99
    @76
    @81
    @82
    @82
    wa
    #
    @98
    @100
    wi
    @65
    @76
    @83
    @78
    adantl
    #
    @81
    @82
    @65
    simpll
    #
    @83
    @101
    @65
    @82
    @81
    @82
    @82
    @81
    ax-1
    imdistanri
    adantr
    @0
    cS
    cN
    cN
    lt2add
    syl21anc
    @99
    @17
    cN
    cN
    @99
    @0
    cS
    @102
    @103
    readdcld
    @81
    @82
    @65
    simplr
    #
    @104
    ltsubaddd
    sylibrd
    ex
    com23
    expcomd
    syl
    3impia
    com13
    3ad2ant2
    sylbi
    imp
    3adant2
    sylbi
    impcom
    3jca
    sylanb
    @18
    cN
    elfzo0
    sylibr
    adantr
    @51
    @30
    @18
    wceq
    #
    wa
    #
    @34
    @38
    @40
    @22
    @26
    @28
    @106
    @31
    @19
    @33
    @21
    @105
    @31
    @19
    wceq
    @51
    @30
    @18
    cP
    fveq2
    #
    adantl
    #
    @105
    @51
    @33
    @47
    cP
    cfv
    @21
    @105
    @32
    @47
    cP
    @30
    @18
    c1
    caddc
    oveq1
    fveq2d
    @51
    @47
    @20
    cP
    @46
    @48
    simpr
    fveq2d
    sylan9eqr
    #
    eqeq12d
    @105
    @38
    @26
    wb
    @51
    @105
    @36
    @24
    @37
    @25
    @105
    @35
    @23
    cI
    @30
    @18
    cF
    fveq2
    fveq2d
    @105
    @31
    @19
    @107
    sneqd
    eqeq12d
    adantl
    @106
    @39
    @27
    @36
    @24
    @106
    @31
    @19
    @33
    @21
    @108
    @109
    preq12d
    @106
    @35
    @23
    cI
    @106
    @30
    @18
    cF
    @51
    @105
    simpr
    fveq2d
    fveq2d
    sseq12d
    ifpbi123d
    rspcdv
    mpdan
    sylan
    ex
    mpid
    imp
    @16
    @1
    @19
    wceq
    #
    @3
    @21
    wceq
    #
    @6
    @24
    wceq
    #
    @11
    @29
    wb
    @15
    wph
    @0
    @13
    cN
    cfz
    co
    #
    wcel
    @110
    @0
    @13
    cN
    elfzofz
    wph
    vx
    cP
    cQ
    cS
    @0
    cN
    crctcshwlkn0lem.s
    crctcshwlkn0lem.q
    crctcshwlkn0lem3
    sylan2
    @15
    wph
    @2
    @113
    wcel
    @111
    @13
    cN
    @0
    fzofzp1
    wph
    vx
    cP
    cQ
    cS
    @2
    cN
    crctcshwlkn0lem.s
    crctcshwlkn0lem.q
    crctcshwlkn0lem3
    sylan2
    @16
    @5
    @23
    cI
    @16
    @5
    @0
    cF
    cS
    ccsh
    co
    #
    cfv
    #
    @23
    @0
    cH
    @114
    crctcshwlkn0lem.h
    fveq1i
    @16
    @115
    @17
    cF
    chash
    cfv
    #
    cmo
    co
    #
    cF
    cfv
    #
    @23
    @16
    cF
    cA
    cword
    wcel
    #
    @66
    @0
    cc0
    @116
    cfzo
    co
    #
    wcel
    @115
    @118
    wceq
    wph
    @119
    @15
    crctcshwlkn0lem.f
    adantr
    wph
    @66
    @15
    wph
    @45
    @66
    crctcshwlkn0lem.s
    @50
    syl
    adantr
    @16
    @0
    @42
    @120
    wph
    @14
    @42
    @0
    wph
    @45
    @13
    cc0
    cuz
    cfv
    wcel
    #
    @14
    @42
    wss
    crctcshwlkn0lem.s
    @45
    @13
    cn0
    wcel
    @121
    @45
    @12
    c1
    @45
    @59
    @12
    cn0
    wcel
    #
    @60
    @59
    cS
    cN
    cle
    wbr
    #
    @122
    @57
    @54
    @58
    @123
    @80
    @83
    @58
    @123
    wi
    @85
    cS
    cN
    ltle
    syl
    3impia
    @59
    cS
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    @123
    @122
    wb
    @57
    @54
    @126
    @58
    @57
    @124
    @54
    @125
    cS
    nnnn0
    cN
    nnnn0
    anim12i
    3adant3
    cS
    cN
    nn0sub
    syl
    mpbid
    sylbi
    c1
    cn0
    wcel
    @45
    1nn0
    a1i
    nn0addcld
    @13
    elnn0uz
    sylib
    @13
    cc0
    cN
    fzoss1
    3syl
    sselda
    cN
    @116
    cc0
    cfzo
    crctcshwlkn0lem.n
    oveq2i
    syl6eleq
    @0
    cS
    cA
    cF
    cshwidxmod
    syl3anc
    @16
    @117
    @18
    cF
    @16
    @117
    @17
    cN
    cmo
    co
    #
    @18
    @116
    cN
    @17
    cmo
    cN
    @116
    crctcshwlkn0lem.n
    eqcomi
    oveq2i
    @16
    @17
    cr
    wcel
    #
    cN
    crp
    wcel
    #
    wa
    @64
    @17
    c2
    cN
    cmul
    co
    clt
    wbr
    #
    wa
    #
    wa
    #
    @127
    @18
    wceq
    wph
    @15
    @132
    wph
    @45
    @15
    @132
    wi
    #
    crctcshwlkn0lem.s
    @45
    @59
    @133
    @60
    @15
    @69
    @59
    @132
    @70
    @59
    @69
    @132
    @59
    @69
    wa
    #
    @128
    @129
    @131
    @134
    @0
    cS
    @69
    @76
    @59
    @67
    @63
    @76
    @68
    @13
    @0
    eluzelre
    3ad2ant1
    adantl
    #
    @59
    @81
    @69
    @57
    @54
    @81
    @58
    @84
    3ad2ant1
    adantr
    #
    readdcld
    @59
    @129
    @69
    @54
    @57
    @129
    @58
    cN
    nnrp
    3ad2ant2
    adantr
    #
    @134
    @64
    @130
    @69
    @59
    @64
    @93
    impcom
    @134
    @0
    cS
    cN
    @135
    @136
    @134
    cN
    @137
    rpred
    @59
    @67
    @63
    @68
    simpr3
    @57
    @54
    @58
    @69
    simpl3
    lt2addmuld
    jca
    jca31
    ex
    syl5bi
    sylbi
    syl
    imp
    @17
    cN
    2submod
    syl
    syl5eq
    fveq2d
    eqtrd
    syl5eq
    fveq2d
    @110
    @111
    @112
    w3a
    #
    @4
    @8
    @10
    @22
    @26
    @28
    @138
    @1
    @19
    @3
    @21
    @110
    @111
    @112
    simp1
    #
    @110
    @111
    @112
    simp2
    #
    eqeq12d
    @138
    @6
    @24
    @7
    @25
    @110
    @111
    @112
    simp3
    #
    @138
    @1
    @19
    @139
    sneqd
    eqeq12d
    @138
    @9
    @27
    @6
    @24
    @138
    @1
    @19
    @3
    @21
    @139
    @140
    preq12d
    @141
    sseq12d
    ifpbi123d
    syl3anc
    mpbird
    ralrimiva
end
