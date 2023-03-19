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
include "cc0.mm"
include "cmin.mm"
include "cfzo.mm"
include "wcel.mm"
include "wa.mm"
include "wral.mm"
include "wi.mm"
include "cc.mm"
include "elfzoelz.mm"
include "zcnd.mm"
include "adantl.mm"
include "adantr.mm"
include "1cnd.mm"
include "add32d.mm"
include "cn0.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "elfzo1.mm"
include "nnnn0.mm"
include "elfzonn0.mm"
include "nn0addcl.mm"
include "ex.mm"
include "syl.mm"
include "syl5com.mm"
include "3ad2ant1.mm"
include "sylbi.mm"
include "imp.mm"
include "fzo0ss1.mm"
include "sseli.mm"
include "elfzo0.mm"
include "simp2bi.mm"
include "cr.mm"
include "wb.mm"
include "nn0re.mm"
include "nnre.mm"
include "anim12i.mm"
include "3adant3.mm"
include "3anass.mm"
include "sylibr.mm"
include "ltaddsub.mm"
include "bicomd.mm"
include "biimpd.mm"
include "com23.mm"
include "a1d.mm"
include "3imp.mm"
include "impcom.mm"
include "syl3anbrc.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "simpr.mm"
include "sylan9eqr.mm"
include "eqeq12d.mm"
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
include "crctcshwlkn0lem2.mm"
include "sylan2.mm"
include "fzofzp1.mm"
include "ccsh.mm"
include "fveq1i.mm"
include "chash.mm"
include "cmo.mm"
include "cword.mm"
include "cz.mm"
include "cuz.mm"
include "cle.mm"
include "nnz.mm"
include "zsubcld.mm"
include "nn0ge0d.mm"
include "subge02.mm"
include "syl2anr.mm"
include "mpbid.mm"
include "3jca.mm"
include "eluz2.mm"
include "fzoss2.mm"
include "3syl.mm"
include "sselda.mm"
include "oveq2i.mm"
include "syl6eleq.mm"
include "cshwidxmod.mm"
include "syl3anc.mm"
include "eqcomi.mm"
include "nnm1nn0.mm"
include "3ad2ant2.mm"
include "nn0zd.mm"
include "zltlem1.mm"
include "syl2anc.mm"
include "sylbid.mm"
include "impancom.mm"
include "3adant2.mm"
include "sylanb.mm"
include "elfz2nn0.mm"
include "zaddcl.mm"
include "zmodid2.mm"
include "mpbird.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "ralrimiva.mm"

theorem crctcshwlkn0lem4
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
  assert |- ( ph -> A. j e. ( 0 ..^ ( N - S ) ) if- ( ( Q ` j ) = ( Q ` ( j + 1 ) ) , ( I ` ( H ` j ) ) = { ( Q ` j ) } , { ( Q ` j ) , ( Q ` ( j + 1 ) ) } C_ ( I ` ( H ` j ) ) ) )

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
    cc0
    cN
    cS
    cmin
    co
    #
    cfzo
    co
    #
    wph
    @0
    @13
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
    cP
    cfv
    #
    @2
    cS
    caddc
    co
    #
    cP
    cfv
    #
    wceq
    #
    @16
    cF
    cfv
    #
    cI
    cfv
    #
    @17
    csn
    #
    wceq
    #
    @17
    @19
    cpr
    #
    @22
    wss
    #
    wif
    #
    wph
    @14
    @27
    wph
    @14
    vi
    cv
    #
    cP
    cfv
    #
    @28
    c1
    caddc
    co
    #
    cP
    cfv
    #
    wceq
    #
    @28
    cF
    cfv
    #
    cI
    cfv
    #
    @29
    csn
    #
    wceq
    #
    @29
    @31
    cpr
    #
    @34
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
    @27
    crctcshwlkn0lem.p
    wph
    @14
    @41
    @27
    wi
    #
    wph
    cS
    c1
    cN
    cfzo
    co
    #
    wcel
    #
    @14
    @42
    crctcshwlkn0lem.s
    @44
    @14
    wa
    #
    @16
    c1
    caddc
    co
    #
    @18
    wceq
    #
    @42
    @45
    @0
    cS
    c1
    @14
    @0
    cc
    wcel
    @44
    @14
    @0
    @0
    cc0
    @12
    elfzoelz
    #
    zcnd
    adantl
    @44
    cS
    cc
    wcel
    @14
    @44
    cS
    cS
    c1
    cN
    elfzoelz
    #
    zcnd
    adantr
    @45
    1cnd
    add32d
    @45
    @47
    wa
    #
    @39
    @27
    vi
    @16
    @40
    @45
    @16
    @40
    wcel
    #
    @47
    @45
    @16
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    @16
    cN
    clt
    wbr
    #
    @51
    @44
    @14
    @52
    @44
    cS
    cn
    wcel
    #
    @53
    cS
    cN
    clt
    wbr
    #
    w3a
    #
    @14
    @52
    wi
    #
    cN
    cS
    elfzo1
    #
    @55
    @53
    @58
    @56
    @55
    cS
    cn0
    wcel
    #
    @14
    @52
    cS
    nnnn0
    #
    @14
    @0
    cn0
    wcel
    #
    @60
    @52
    wi
    @0
    @12
    elfzonn0
    @62
    @60
    @52
    @0
    cS
    nn0addcl
    #
    ex
    syl
    syl5com
    3ad2ant1
    #
    sylbi
    imp
    @44
    @53
    @14
    @44
    cS
    @40
    wcel
    #
    @53
    @43
    @40
    cS
    cN
    fzo0ss1
    sseli
    @65
    @60
    @53
    @56
    cS
    cN
    elfzo0
    simp2bi
    syl
    adantr
    #
    @14
    @44
    @54
    @14
    @62
    @12
    cn
    wcel
    #
    @0
    @12
    clt
    wbr
    #
    w3a
    #
    @44
    @54
    wi
    #
    @0
    @12
    elfzo0
    #
    @62
    @67
    @68
    @70
    @62
    @68
    @70
    wi
    @67
    @62
    @44
    @68
    @54
    @62
    @44
    @68
    @54
    wi
    @62
    @44
    wa
    #
    @68
    @54
    @72
    @0
    cr
    wcel
    #
    cS
    cr
    wcel
    #
    cN
    cr
    wcel
    #
    w3a
    #
    @68
    @54
    wb
    #
    @72
    @73
    @74
    @75
    wa
    #
    wa
    #
    @76
    @62
    @73
    @44
    @78
    @0
    nn0re
    #
    @44
    @57
    @78
    @59
    @55
    @53
    @78
    @56
    @55
    @74
    @53
    @75
    cS
    nnre
    #
    cN
    nnre
    #
    anim12i
    3adant3
    #
    sylbi
    anim12i
    @73
    @74
    @75
    3anass
    #
    sylibr
    @76
    @54
    @68
    @0
    cS
    cN
    ltaddsub
    bicomd
    #
    syl
    biimpd
    ex
    com23
    a1d
    3imp
    sylbi
    impcom
    @16
    cN
    elfzo0
    syl3anbrc
    adantr
    @50
    @28
    @16
    wceq
    #
    wa
    #
    @32
    @36
    @38
    @20
    @24
    @26
    @87
    @29
    @17
    @31
    @19
    @86
    @29
    @17
    wceq
    @50
    @28
    @16
    cP
    fveq2
    #
    adantl
    #
    @86
    @50
    @31
    @46
    cP
    cfv
    @19
    @86
    @30
    @46
    cP
    @28
    @16
    c1
    caddc
    oveq1
    fveq2d
    @50
    @46
    @18
    cP
    @45
    @47
    simpr
    fveq2d
    sylan9eqr
    #
    eqeq12d
    @86
    @36
    @24
    wb
    @50
    @86
    @34
    @22
    @35
    @23
    @86
    @33
    @21
    cI
    @28
    @16
    cF
    fveq2
    fveq2d
    #
    @86
    @29
    @17
    @88
    sneqd
    eqeq12d
    adantl
    @87
    @37
    @25
    @34
    @22
    @87
    @29
    @17
    @31
    @19
    @89
    @90
    preq12d
    @86
    @34
    @22
    wceq
    @50
    @91
    adantl
    sseq12d
    ifpbi123d
    rspcdv
    mpdan
    sylan
    ex
    mpid
    imp
    @15
    @1
    @17
    wceq
    #
    @3
    @19
    wceq
    #
    @6
    @22
    wceq
    #
    @11
    @27
    wb
    @14
    wph
    @0
    cc0
    @12
    cfz
    co
    #
    wcel
    @92
    @0
    cc0
    @12
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
    crctcshwlkn0lem2
    sylan2
    @14
    wph
    @2
    @95
    wcel
    @93
    cc0
    @12
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
    crctcshwlkn0lem2
    sylan2
    @15
    @5
    @21
    cI
    @15
    @5
    @0
    cF
    cS
    ccsh
    co
    #
    cfv
    #
    @21
    @0
    cH
    @96
    crctcshwlkn0lem.h
    fveq1i
    @15
    @97
    @16
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
    @21
    @15
    cF
    cA
    cword
    wcel
    #
    cS
    cz
    wcel
    #
    @0
    cc0
    @98
    cfzo
    co
    #
    wcel
    @97
    @100
    wceq
    wph
    @101
    @14
    crctcshwlkn0lem.f
    adantr
    wph
    @102
    @14
    wph
    @44
    @102
    crctcshwlkn0lem.s
    @49
    syl
    adantr
    @15
    @0
    @40
    @103
    wph
    @13
    @40
    @0
    wph
    @44
    cN
    @12
    cuz
    cfv
    wcel
    #
    @13
    @40
    wss
    crctcshwlkn0lem.s
    @44
    @12
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @12
    cN
    cle
    wbr
    #
    w3a
    #
    @104
    @44
    @57
    @108
    @59
    @55
    @53
    @108
    @56
    @55
    @53
    wa
    #
    @105
    @106
    @107
    @109
    cN
    cS
    @53
    @106
    @55
    cN
    nnz
    #
    adantl
    #
    @55
    @102
    @53
    cS
    nnz
    adantr
    zsubcld
    @111
    @109
    cc0
    cS
    cle
    wbr
    #
    @107
    @55
    @112
    @53
    @55
    cS
    @61
    nn0ge0d
    adantr
    @53
    @75
    @74
    @112
    @107
    wb
    @55
    @82
    @81
    cN
    cS
    subge02
    syl2anr
    mpbid
    3jca
    3adant3
    sylbi
    @12
    cN
    eluz2
    sylibr
    @12
    cc0
    cN
    fzoss2
    3syl
    sselda
    cN
    @98
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
    @15
    @99
    @16
    cF
    @15
    @99
    @16
    cN
    cmo
    co
    #
    @16
    @98
    cN
    @16
    cmo
    cN
    @98
    crctcshwlkn0lem.n
    eqcomi
    oveq2i
    wph
    @44
    @14
    @113
    @16
    wceq
    #
    crctcshwlkn0lem.s
    @45
    @114
    @16
    cc0
    cN
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    @45
    @52
    @115
    cn0
    wcel
    #
    @16
    @115
    cle
    wbr
    #
    w3a
    #
    @116
    @44
    @57
    @14
    @119
    @59
    @57
    @14
    wa
    @52
    @117
    @118
    @57
    @14
    @52
    @64
    imp
    @57
    @117
    @14
    @53
    @55
    @117
    @56
    cN
    nnm1nn0
    3ad2ant2
    adantr
    @14
    @57
    @118
    @14
    @69
    @57
    @118
    wi
    #
    @71
    @62
    @68
    @120
    @67
    @62
    @57
    @68
    @118
    @62
    @57
    wa
    #
    @68
    @54
    @118
    @121
    @76
    @77
    @121
    @79
    @76
    @62
    @73
    @57
    @78
    @80
    @83
    anim12i
    @84
    sylibr
    @85
    syl
    @121
    @54
    @118
    @121
    @16
    cz
    wcel
    #
    @106
    @54
    @118
    wb
    @121
    @16
    @57
    @62
    @60
    @52
    @55
    @53
    @60
    @56
    @61
    3ad2ant1
    @63
    sylan2
    nn0zd
    @57
    @106
    @62
    @53
    @55
    @106
    @56
    @110
    3ad2ant2
    adantl
    @16
    cN
    zltlem1
    syl2anc
    biimpd
    sylbid
    impancom
    3adant2
    sylbi
    impcom
    3jca
    sylanb
    @16
    @115
    elfz2nn0
    sylibr
    @45
    @122
    @53
    @114
    @116
    wb
    @14
    @0
    cz
    wcel
    @102
    @122
    @44
    @48
    @49
    @0
    cS
    zaddcl
    syl2anr
    @66
    @16
    cN
    zmodid2
    syl2anc
    mpbird
    sylan
    syl5eq
    fveq2d
    eqtrd
    syl5eq
    fveq2d
    @92
    @93
    @94
    w3a
    #
    @4
    @8
    @10
    @20
    @24
    @26
    @123
    @1
    @17
    @3
    @19
    @92
    @93
    @94
    simp1
    #
    @92
    @93
    @94
    simp2
    #
    eqeq12d
    @123
    @6
    @22
    @7
    @23
    @92
    @93
    @94
    simp3
    #
    @123
    @1
    @17
    @124
    sneqd
    eqeq12d
    @123
    @9
    @25
    @6
    @22
    @123
    @1
    @17
    @3
    @19
    @124
    @125
    preq12d
    @126
    sseq12d
    ifpbi123d
    syl3anc
    mpbird
    ralrimiva
end
