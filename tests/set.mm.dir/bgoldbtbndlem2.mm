include "codd.mm"
include "wcel.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "w3a.mm"
include "cmin.mm"
include "cfv.mm"
include "cprime.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "caddc.mm"
include "c4.mm"
include "clt.mm"
include "wbr.mm"
include "cico.mm"
include "cle.mm"
include "wa.mm"
include "ceven.mm"
include "wi.mm"
include "cv.mm"
include "cc0.mm"
include "wral.mm"
include "cz.mm"
include "elfzoelz.mm"
include "elfzoel2.mm"
include "elfzom1b.mm"
include "wss.mm"
include "fzossrbm1.mm"
include "adantl.mm"
include "sseld.mm"
include "sylbid.mm"
include "com12.mm"
include "mp2and.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "breq1d.mm"
include "breq2d.mm"
include "3anbi123d.mm"
include "rspcv.mm"
include "syl.mm"
include "syl5com.mm"
include "a1d.mm"
include "3imp.mm"
include "simp2.mm"
include "oddprmALTV.mm"
include "3ad2ant1.mm"
include "anim12i.mm"
include "adantr.mm"
include "omoeALTV.mm"
include "syl5eqel.mm"
include "wb.mm"
include "cc.mm"
include "zcnd.mm"
include "3ad2ant3.mm"
include "npcan1.mm"
include "oveq1d.mm"
include "eldifi.mm"
include "prmz.mm"
include "cr.mm"
include "zre.mm"
include "simp1.mm"
include "ralimi.mm"
include "fzo0ss1.mm"
include "sseli.mm"
include "ex.mm"
include "com23.mm"
include "a1i.mm"
include "com13.mm"
include "mpcom.mm"
include "cdc.mm"
include "cuz.mm"
include "eluzelz.mm"
include "oddz.mm"
include "zred.mm"
include "simplr.mm"
include "simprl.mm"
include "4re.mm"
include "lesubaddd.mm"
include "simpllr.mm"
include "simplrr.mm"
include "resubcld.mm"
include "simplrl.mm"
include "readdcld.mm"
include "simplll.mm"
include "simprr.mm"
include "lesub1d.mm"
include "biimpa.mm"
include "adantrr.mm"
include "resubcl.mm"
include "simpll.mm"
include "ltaddsub2.mm"
include "bicomd.mm"
include "syl3anc.mm"
include "biimpd.mm"
include "adantld.mm"
include "imp.mm"
include "4cn.mm"
include "recnd.mm"
include "recn.mm"
include "addsubassd.mm"
include "mpbird.mm"
include "lelttrd.mm"
include "exp32.mm"
include "sylan2.mm"
include "3syl.mm"
include "3adant3.mm"
include "impcom.mm"
include "expcom.mm"
include "syl5eqbr.mm"
include "1eluzge0.mm"
include "fzoss1.mm"
include "mp1i.mm"
include "sselda.mm"
include "syl6.mm"
include "mpid.mm"
include "3adant2.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "3ad2ant2.mm"
include "syl2an.mm"
include "biimpcd.mm"
include "cxr.mm"
include "cn.mm"
include "c3.mm"
include "eluzge3nn.mm"
include "ciccp.mm"
include "cfz.mm"
include "fzossfz.mm"
include "syl6ss.mm"
include "iccpartxr.mm"
include "fzofzp1.mm"
include "jca.mm"
include "elico1.mm"
include "syl6bi.mm"
include "adantrd.mm"
include "lesub1dd.mm"
include "ltletrd.mm"
include "syl6breqr.mm"
include "3jca.mm"
include "mpdan.mm"

theorem bgoldbtbndlem2
  let wph: wff ph
  let cD: class D
  let cS: class S
  let vi: setvar i
  let vn: setvar n
  let cF: class F
  let cI: class I
  let cM: class M
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume bgoldbtbnd.m: |- ( ph -> M e. ( ZZ>= ` ; 1 1 ) )
  assume bgoldbtbnd.n: |- ( ph -> N e. ( ZZ>= ` ; 1 1 ) )
  assume bgoldbtbnd.b: |- ( ph -> A. n e. Even ( ( 4 < n /\ n < N ) -> n e. GoldbachEven ) )
  assume bgoldbtbnd.d: |- ( ph -> D e. ( ZZ>= ` 3 ) )
  assume bgoldbtbnd.f: |- ( ph -> F e. ( RePart ` D ) )
  assume bgoldbtbnd.i: |- ( ph -> A. i e. ( 0 ..^ D ) ( ( F ` i ) e. ( Prime \ { 2 } ) /\ ( ( F ` ( i + 1 ) ) - ( F ` i ) ) < ( N - 4 ) /\ 4 < ( ( F ` ( i + 1 ) ) - ( F ` i ) ) ) )
  assume bgoldbtbnd.0: |- ( ph -> ( F ` 0 ) = 7 )
  assume bgoldbtbnd.1: |- ( ph -> ( F ` 1 ) = ; 1 3 )
  assume bgoldbtbnd.l: |- ( ph -> M < ( F ` D ) )
  assume bgoldbtbndlem2.s: |- S = ( X - ( F ` ( I - 1 ) ) )

  disjoint D i
  disjoint F i
  disjoint I i
  disjoint N i
  disjoint k x
  assert |- ( ( ph /\ X e. Odd /\ I e. ( 1 ..^ D ) ) -> ( ( X e. ( ( F ` I ) [,) ( F ` ( I + 1 ) ) ) /\ ( X - ( F ` I ) ) <_ 4 ) -> ( S e. Even /\ S < N /\ 4 < S ) ) )

  proof
    wph
    cX
    codd
    wcel
    #
    cI
    c1
    cD
    cfzo
    co
    #
    wcel
    #
    w3a
    #
    cI
    c1
    cmin
    co
    #
    cF
    cfv
    #
    cprime
    c2
    csn
    #
    cdif
    #
    wcel
    #
    @4
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @5
    cmin
    co
    #
    cN
    c4
    cmin
    co
    #
    clt
    wbr
    #
    c4
    @11
    clt
    wbr
    #
    w3a
    #
    cX
    cI
    cF
    cfv
    #
    cI
    c1
    caddc
    co
    #
    cF
    cfv
    #
    cico
    co
    wcel
    #
    cX
    @16
    cmin
    co
    c4
    cle
    wbr
    #
    wa
    #
    cS
    ceven
    wcel
    #
    cS
    cN
    clt
    wbr
    #
    c4
    cS
    clt
    wbr
    #
    w3a
    #
    wi
    wph
    @0
    @2
    @15
    wph
    @2
    @15
    wi
    @0
    wph
    vi
    cv
    #
    cF
    cfv
    #
    @7
    wcel
    #
    @26
    c1
    caddc
    co
    #
    cF
    cfv
    #
    @27
    cmin
    co
    #
    @12
    clt
    wbr
    #
    c4
    @31
    clt
    wbr
    #
    w3a
    #
    vi
    cc0
    cD
    cfzo
    co
    #
    wral
    #
    @2
    @15
    bgoldbtbnd.i
    @2
    @4
    @35
    wcel
    #
    @36
    @15
    wi
    @2
    cI
    cz
    wcel
    #
    cD
    cz
    wcel
    #
    @37
    cI
    c1
    cD
    elfzoelz
    #
    cI
    c1
    cD
    elfzoel2
    @38
    @39
    wa
    #
    @2
    @37
    @41
    @2
    @4
    cc0
    cD
    c1
    cmin
    co
    cfzo
    co
    #
    wcel
    @37
    cI
    cD
    elfzom1b
    @41
    @42
    @35
    @4
    @39
    @42
    @35
    wss
    @38
    cD
    fzossrbm1
    adantl
    sseld
    sylbid
    com12
    mp2and
    @34
    @15
    vi
    @4
    @35
    @26
    @4
    wceq
    #
    @28
    @8
    @32
    @13
    @33
    @14
    @43
    @27
    @5
    @7
    @26
    @4
    cF
    fveq2
    #
    eleq1d
    @43
    @31
    @11
    @12
    clt
    @43
    @30
    @10
    @27
    @5
    cmin
    @43
    @29
    @9
    cF
    @26
    @4
    c1
    caddc
    oveq1
    fveq2d
    @44
    oveq12d
    #
    breq1d
    @43
    @31
    @11
    c4
    clt
    @45
    breq2d
    3anbi123d
    rspcv
    syl
    syl5com
    a1d
    3imp
    @3
    @15
    wa
    #
    @21
    @25
    @46
    @21
    wa
    #
    @22
    @23
    @24
    @47
    cS
    cX
    @5
    cmin
    co
    #
    ceven
    bgoldbtbndlem2.s
    @47
    @0
    @5
    codd
    wcel
    #
    wa
    #
    @48
    ceven
    wcel
    @46
    @50
    @21
    @3
    @0
    @15
    @49
    wph
    @0
    @2
    simp2
    @8
    @13
    @49
    @14
    @5
    oddprmALTV
    3ad2ant1
    anim12i
    adantr
    cX
    @5
    omoeALTV
    syl
    syl5eqel
    @47
    cS
    @48
    cN
    clt
    bgoldbtbndlem2.s
    @21
    @46
    @48
    cN
    clt
    wbr
    #
    @20
    @46
    @51
    wi
    @19
    @46
    @20
    @51
    @15
    @3
    @20
    @51
    wi
    #
    @8
    @13
    @3
    @52
    wi
    #
    @14
    @8
    @13
    @53
    @8
    @3
    @13
    @52
    @3
    @8
    @13
    @52
    wi
    @3
    @8
    wa
    @13
    @16
    @5
    cmin
    co
    #
    @12
    clt
    wbr
    #
    @52
    @3
    @13
    @55
    wb
    @8
    @3
    @11
    @54
    @12
    clt
    @3
    @10
    @16
    @5
    cmin
    @3
    @9
    cI
    cF
    @3
    cI
    cc
    wcel
    #
    @9
    cI
    wceq
    #
    @2
    wph
    @56
    @0
    @2
    cI
    @40
    zcnd
    #
    3ad2ant3
    cI
    npcan1
    #
    syl
    fveq2d
    oveq1d
    breq1d
    adantr
    @8
    @3
    @55
    @52
    wi
    #
    @8
    @5
    cprime
    wcel
    #
    @5
    cz
    wcel
    #
    @3
    @60
    wi
    @5
    cprime
    @6
    eldifi
    #
    @5
    prmz
    #
    @62
    @5
    cr
    wcel
    #
    @3
    @60
    @5
    zre
    @16
    @7
    wcel
    #
    @3
    @65
    @60
    wi
    #
    wph
    @0
    @2
    @66
    @36
    wph
    @0
    @2
    @66
    wi
    #
    wi
    #
    bgoldbtbnd.i
    @36
    @28
    vi
    @35
    wral
    #
    wph
    @69
    wi
    @34
    @28
    vi
    @35
    @28
    @32
    @33
    simp1
    ralimi
    @0
    wph
    @70
    @68
    wph
    @70
    @68
    wi
    wi
    @0
    wph
    @2
    @70
    @66
    wph
    @2
    @70
    @66
    wi
    #
    wph
    @2
    wa
    #
    cI
    @35
    wcel
    #
    @71
    @2
    @73
    wph
    @1
    @35
    cI
    cD
    fzo0ss1
    sseli
    adantl
    @28
    @66
    vi
    cI
    @35
    @26
    cI
    wceq
    #
    @27
    @16
    @7
    @26
    cI
    cF
    fveq2
    #
    eleq1d
    #
    rspcv
    syl
    ex
    com23
    a1i
    com13
    syl
    mpcom
    3imp
    @66
    @16
    cprime
    wcel
    #
    @16
    cz
    wcel
    #
    @3
    @67
    wi
    @16
    cprime
    @6
    eldifi
    #
    @16
    prmz
    #
    @78
    @16
    cr
    wcel
    #
    @3
    @67
    @16
    zre
    wph
    @0
    @81
    @67
    wi
    #
    @2
    wph
    @0
    @82
    wph
    cN
    c1
    c1
    cdc
    #
    cuz
    cfv
    wcel
    cN
    cz
    wcel
    #
    @0
    @82
    wi
    #
    bgoldbtbnd.n
    @83
    cN
    eluzelz
    @84
    cN
    cr
    wcel
    #
    @85
    cN
    zre
    @86
    @0
    @82
    @0
    @86
    cX
    cr
    wcel
    #
    @82
    @0
    cX
    cX
    oddz
    zred
    #
    @86
    @87
    wa
    #
    @81
    @65
    @60
    @89
    @81
    @65
    wa
    #
    wa
    #
    @20
    @55
    @51
    @91
    @20
    cX
    c4
    @16
    caddc
    co
    #
    cle
    wbr
    #
    @55
    @51
    wi
    @91
    cX
    @16
    c4
    @86
    @87
    @90
    simplr
    #
    @89
    @81
    @65
    simprl
    #
    c4
    cr
    wcel
    #
    @91
    4re
    a1i
    #
    lesubaddd
    @91
    @93
    @55
    @51
    @91
    @93
    @55
    wa
    #
    wa
    #
    @48
    @92
    @5
    cmin
    co
    #
    cN
    @99
    cX
    @5
    @86
    @87
    @90
    @98
    simpllr
    @89
    @81
    @65
    @98
    simplrr
    #
    resubcld
    @99
    @92
    @5
    @99
    c4
    @16
    @96
    @99
    4re
    a1i
    @89
    @81
    @65
    @98
    simplrl
    readdcld
    @101
    resubcld
    @86
    @87
    @90
    @98
    simplll
    @91
    @93
    @48
    @100
    cle
    wbr
    #
    @55
    @91
    @93
    @102
    @91
    cX
    @92
    @5
    @94
    @91
    c4
    @16
    @97
    @95
    readdcld
    @89
    @81
    @65
    simprr
    lesub1d
    biimpa
    adantrr
    @99
    @100
    cN
    clt
    wbr
    #
    c4
    @54
    caddc
    co
    #
    cN
    clt
    wbr
    #
    @91
    @98
    @105
    @91
    @55
    @105
    @93
    @91
    @55
    @105
    @91
    @96
    @54
    cr
    wcel
    #
    @86
    @55
    @105
    wb
    @97
    @90
    @106
    @89
    @16
    @5
    resubcl
    adantl
    @86
    @87
    @90
    simpll
    @96
    @106
    @86
    w3a
    @105
    @55
    c4
    @54
    cN
    ltaddsub2
    bicomd
    syl3anc
    biimpd
    adantld
    imp
    @91
    @103
    @105
    wb
    @98
    @91
    @100
    @104
    cN
    clt
    @91
    c4
    @16
    @5
    c4
    cc
    wcel
    @91
    4cn
    a1i
    @91
    @16
    @95
    recnd
    @90
    @5
    cc
    wcel
    #
    @89
    @65
    @107
    @81
    @5
    recn
    adantl
    adantl
    addsubassd
    breq1d
    adantr
    mpbird
    lelttrd
    exp32
    sylbid
    com23
    exp32
    sylan2
    ex
    syl
    3syl
    imp
    3adant3
    syl5com
    3syl
    mpcom
    syl5com
    3syl
    impcom
    sylbid
    expcom
    com23
    imp
    3adant3
    impcom
    com12
    adantl
    impcom
    syl5eqbr
    @47
    c4
    @48
    cS
    clt
    @47
    c4
    @54
    @48
    @96
    @47
    4re
    a1i
    @47
    @16
    @5
    @3
    @81
    @15
    @21
    wph
    @2
    @81
    @0
    wph
    @2
    @81
    wph
    @2
    @36
    @81
    bgoldbtbnd.i
    wph
    @2
    @36
    @81
    wi
    @72
    @36
    @66
    @18
    @16
    cmin
    co
    #
    @12
    clt
    wbr
    #
    c4
    @108
    clt
    wbr
    #
    w3a
    #
    @81
    @72
    @73
    @36
    @111
    wi
    wph
    @1
    @35
    cI
    c1
    cc0
    cuz
    cfv
    wcel
    #
    @1
    @35
    wss
    #
    wph
    1eluzge0
    c1
    cc0
    cD
    fzoss1
    #
    mp1i
    sselda
    #
    @34
    @111
    vi
    cI
    @35
    @74
    @28
    @66
    @32
    @109
    @33
    @110
    @76
    @74
    @31
    @108
    @12
    clt
    @74
    @30
    @18
    @27
    @16
    cmin
    @74
    @29
    @17
    cF
    @26
    cI
    c1
    caddc
    oveq1
    fveq2d
    @75
    oveq12d
    #
    breq1d
    @74
    @31
    @108
    c4
    clt
    @116
    breq2d
    3anbi123d
    rspcv
    syl
    @66
    @109
    @81
    @110
    @66
    @77
    @81
    @79
    @77
    @16
    @80
    zred
    syl
    3ad2ant1
    syl6
    ex
    mpid
    imp
    3adant2
    ad2antrr
    #
    @15
    @65
    @3
    @21
    @8
    @13
    @65
    @14
    @8
    @61
    @65
    @63
    @61
    @5
    @64
    zred
    syl
    3ad2ant1
    #
    ad2antlr
    #
    resubcld
    @46
    @48
    cr
    wcel
    #
    @21
    @3
    @87
    @65
    @120
    @15
    @0
    wph
    @87
    @2
    @88
    3ad2ant2
    #
    @118
    cX
    @5
    resubcl
    syl2an
    adantr
    @46
    c4
    @54
    clt
    wbr
    #
    @21
    @15
    @3
    @122
    @14
    @8
    @3
    @122
    wi
    @13
    @3
    @14
    @122
    @3
    @11
    @54
    c4
    clt
    @3
    @10
    @16
    @5
    cmin
    @3
    @9
    cI
    cF
    @2
    wph
    @57
    @0
    @2
    @56
    @57
    @58
    @59
    syl
    3ad2ant3
    fveq2d
    oveq1d
    breq2d
    biimpcd
    3ad2ant3
    impcom
    adantr
    @47
    @16
    cX
    @5
    @117
    @3
    @87
    @15
    @21
    @121
    ad2antrr
    @119
    @46
    @21
    @16
    cX
    cle
    wbr
    #
    @3
    @21
    @123
    wi
    @15
    @3
    @19
    @123
    @20
    @3
    @19
    cX
    cxr
    wcel
    #
    @123
    cX
    @18
    clt
    wbr
    #
    w3a
    #
    @123
    @3
    @16
    cxr
    wcel
    #
    @18
    cxr
    wcel
    #
    wa
    #
    @19
    @126
    wb
    wph
    @2
    @129
    @0
    @72
    @127
    @128
    @72
    cF
    cI
    cD
    wph
    cD
    cn
    wcel
    #
    @2
    wph
    cD
    c3
    cuz
    cfv
    wcel
    #
    @130
    bgoldbtbnd.d
    cD
    eluzge3nn
    syl
    adantr
    #
    wph
    cF
    cD
    ciccp
    cfv
    wcel
    @2
    bgoldbtbnd.f
    adantr
    #
    wph
    @1
    cc0
    cD
    cfz
    co
    #
    cI
    wph
    @131
    @1
    @134
    wss
    bgoldbtbnd.d
    @131
    @1
    @35
    @134
    @112
    @113
    @131
    1eluzge0
    @114
    mp1i
    cc0
    cD
    fzossfz
    syl6ss
    syl
    sselda
    iccpartxr
    @72
    cF
    @17
    cD
    @132
    @133
    @72
    @73
    @17
    @134
    wcel
    @115
    cc0
    cD
    cI
    fzofzp1
    syl
    iccpartxr
    jca
    3adant2
    @16
    @18
    cX
    elico1
    syl
    @124
    @123
    @125
    simp2
    syl6bi
    adantrd
    adantr
    imp
    lesub1dd
    ltletrd
    bgoldbtbndlem2.s
    syl6breqr
    3jca
    ex
    mpdan
end
