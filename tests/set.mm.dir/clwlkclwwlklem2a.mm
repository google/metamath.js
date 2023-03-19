include "cdm.mm"
include "wf1.mm"
include "cword.mm"
include "wcel.mm"
include "c2.mm"
include "chash.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "clsw.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "crn.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "cfz.mm"
include "wf.mm"
include "clt.mm"
include "ccnv.mm"
include "cif.mm"
include "wn.mm"
include "wo.mm"
include "simpl.mm"
include "wf1o.mm"
include "f1f1orn.mm"
include "3ad2ant1.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "wi.mm"
include "cn0.mm"
include "cn.mm"
include "elfzo0.mm"
include "lencl.mm"
include "cz.mm"
include "elnn0z.mm"
include "cr.mm"
include "0red.mm"
include "zre.mm"
include "nn0re.mm"
include "2re.mm"
include "a1i.mm"
include "resubcld.mm"
include "adantl.mm"
include "lelttr.mm"
include "syl3anc.mm"
include "nn0z.mm"
include "2z.mm"
include "zsubcld.mm"
include "anim1i.mm"
include "elnnz.mm"
include "sylibr.mm"
include "wb.mm"
include "cc.mm"
include "nn0cn.mm"
include "peano2cnm.mm"
include "syl.mm"
include "subid1d.mm"
include "oveq1d.mm"
include "1cnd.mm"
include "subsub4d.mm"
include "1p1e2.mm"
include "oveq2d.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "mpbird.mm"
include "ex.mm"
include "syld.mm"
include "exp4b.mm"
include "com23.mm"
include "imp.mm"
include "sylbi.mm"
include "com12.mm"
include "impcom.mm"
include "df-2.mm"
include "eqcomd.mm"
include "3eqtr2d.mm"
include "breq2d.mm"
include "biimpcd.mm"
include "syl3anbrc.mm"
include "exp32.mm"
include "a1d.mm"
include "com24.mm"
include "com25.mm"
include "3adant2.mm"
include "com14.mm"
include "3adant1.mm"
include "syl7bi.mm"
include "com13.mm"
include "imp31.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "preq12d.mm"
include "rspcdv.mm"
include "expdimp.mm"
include "f1ocnvdm.mm"
include "syl2anc.mm"
include "jca.mm"
include "orcd.mm"
include "peano2zm.mm"
include "anim12i.mm"
include "zltlem1.mm"
include "biimpd.mm"
include "sylbid.mm"
include "impancom.mm"
include "lenlt.mm"
include "mpbid.mm"
include "ancomd.mm"
include "lttri3.mm"
include "exp31.mm"
include "syl5com.mm"
include "3ad2ant2.mm"
include "preq1d.mm"
include "olcd.mm"
include "pm2.61ian.mm"
include "ifel.mm"
include "fmptd.mm"
include "iswrdi.mm"
include "wrdf.mm"
include "clwlkclwwlklem2a2.mm"
include "fzoval.mm"
include "3syl.mm"
include "oveq2.mm"
include "eqcoms.mm"
include "sylan9eq.mm"
include "syldan.mm"
include "feq2d.mm"
include "clwlkclwwlklem2a1.mm"
include "clwlkclwwlklem2a4.mm"
include "impl.mm"
include "ralimdva.mm"
include "raleqdv.mm"
include "imbi2d.mm"
include "syl5ibr.mm"
include "mpcom.mm"
include "adantrr.mm"
include "mpd.mm"
include "3jca.mm"
include "clwlkclwwlklem2a3.mm"
include "eqeq2d.mm"

theorem clwlkclwwlklem2a
  let vx: setvar x
  let cP: class P
  let cR: class R
  let vi: setvar i
  let cE: class E
  let cF: class F
  let cV: class V
  let cI: class I
  assume clwlkclwwlklem2.f: |- F = ( x e. ( 0 ..^ ( ( # ` P ) - 1 ) ) |-> if ( x < ( ( # ` P ) - 2 ) , ( `' E ` { ( P ` x ) , ( P ` ( x + 1 ) ) } ) , ( `' E ` { ( P ` x ) , ( P ` 0 ) } ) ) )

  disjoint P x
  disjoint E x
  disjoint V x
  disjoint E i
  disjoint F i
  disjoint P i
  disjoint R i
  disjoint R x
  disjoint i x
  disjoint V i
  disjoint I x
  assert |- ( ( E : dom E -1-1-> R /\ P e. Word V /\ 2 <_ ( # ` P ) ) -> ( ( ( lastS ` P ) = ( P ` 0 ) /\ ( A. i e. ( 0 ..^ ( ( ( ( # ` P ) - 1 ) - 0 ) - 1 ) ) { ( P ` i ) , ( P ` ( i + 1 ) ) } e. ran E /\ { ( P ` ( ( # ` P ) - 2 ) ) , ( P ` 0 ) } e. ran E ) ) -> ( ( F e. Word dom E /\ P : ( 0 ... ( # ` F ) ) --> V /\ A. i e. ( 0 ..^ ( # ` F ) ) ( E ` ( F ` i ) ) = { ( P ` i ) , ( P ` ( i + 1 ) ) } ) /\ ( P ` 0 ) = ( P ` ( # ` F ) ) ) ) )

  proof
    cE
    cdm
    #
    cR
    cE
    wf1
    #
    cP
    cV
    cword
    wcel
    #
    c2
    cP
    chash
    cfv
    #
    cle
    wbr
    #
    w3a
    #
    cP
    clsw
    cfv
    #
    cc0
    cP
    cfv
    #
    wceq
    #
    vi
    cv
    #
    cP
    cfv
    #
    @9
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    cE
    crn
    #
    wcel
    #
    vi
    cc0
    @3
    c1
    cmin
    co
    #
    cc0
    cmin
    co
    #
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @3
    c2
    cmin
    co
    #
    cP
    cfv
    #
    @7
    cpr
    #
    @14
    wcel
    #
    wa
    #
    wa
    #
    cF
    @0
    cword
    wcel
    #
    cc0
    cF
    chash
    cfv
    #
    cfz
    co
    #
    cV
    cP
    wf
    #
    @9
    cF
    cfv
    cE
    cfv
    @13
    wceq
    #
    vi
    cc0
    @28
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @7
    @28
    cP
    cfv
    #
    wceq
    #
    wa
    @5
    @26
    wa
    #
    @34
    @36
    @37
    @27
    @30
    @33
    @37
    cc0
    @16
    cfzo
    co
    #
    @0
    cF
    wf
    @27
    @37
    vx
    @38
    vx
    cv
    #
    @21
    clt
    wbr
    #
    @39
    cP
    cfv
    #
    @39
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    cE
    ccnv
    #
    cfv
    #
    @41
    @7
    cpr
    #
    @45
    cfv
    #
    cif
    #
    @0
    cF
    @37
    @39
    @38
    wcel
    #
    wa
    #
    @40
    @46
    @0
    wcel
    #
    wa
    #
    @40
    wn
    #
    @48
    @0
    wcel
    #
    wa
    #
    wo
    #
    @49
    @0
    wcel
    @40
    @51
    @57
    @40
    @51
    wa
    #
    @53
    @56
    @58
    @40
    @52
    @40
    @51
    simpl
    @58
    @0
    @14
    cE
    wf1o
    #
    @44
    @14
    wcel
    #
    @52
    @37
    @59
    @40
    @50
    @5
    @59
    @26
    @1
    @2
    @59
    @4
    @0
    cR
    cE
    f1f1orn
    3ad2ant1
    adantr
    #
    ad2antrl
    @51
    @40
    @60
    @37
    @50
    @40
    @60
    @26
    @5
    @50
    @40
    wa
    #
    @60
    wi
    #
    @20
    @5
    @63
    wi
    @8
    @24
    @62
    @5
    @20
    @60
    @62
    @5
    @20
    @60
    wi
    @62
    @5
    wa
    #
    @15
    @60
    vi
    @39
    @19
    @50
    @40
    @5
    @39
    @19
    wcel
    #
    @5
    @40
    @50
    @65
    @50
    @39
    cn0
    wcel
    #
    @16
    cn
    wcel
    #
    @39
    @16
    clt
    wbr
    #
    w3a
    #
    @5
    @40
    @65
    @39
    @16
    elfzo0
    #
    @2
    @4
    @40
    @69
    @65
    wi
    wi
    #
    @1
    @2
    @4
    @71
    @2
    @3
    cn0
    wcel
    #
    @4
    @71
    wi
    cV
    cP
    lencl
    #
    @69
    @4
    @40
    @72
    @65
    @66
    @68
    @4
    @40
    @72
    @65
    wi
    wi
    wi
    #
    @67
    @66
    @68
    @74
    @66
    @72
    @4
    @40
    @68
    @65
    @66
    @72
    @4
    @40
    @68
    @65
    wi
    wi
    wi
    @66
    @72
    wa
    #
    @68
    @40
    @4
    @65
    @75
    @40
    @4
    @65
    wi
    wi
    @68
    @75
    @40
    @4
    @65
    @75
    @40
    @4
    wa
    #
    wa
    @66
    @18
    cn
    wcel
    #
    @39
    @18
    clt
    wbr
    #
    @65
    @75
    @66
    @76
    @66
    @72
    simpl
    adantr
    @76
    @75
    @77
    @40
    @75
    @77
    wi
    @4
    @75
    @40
    @77
    @66
    @72
    @40
    @77
    wi
    #
    @66
    @39
    cz
    wcel
    #
    cc0
    @39
    cle
    wbr
    #
    wa
    @72
    @79
    wi
    #
    @39
    elnn0z
    @80
    @81
    @82
    @80
    @72
    @81
    @79
    @80
    @72
    @81
    @40
    @77
    @80
    @72
    wa
    #
    @81
    @40
    wa
    #
    cc0
    @21
    clt
    wbr
    #
    @77
    @83
    cc0
    cr
    wcel
    @39
    cr
    wcel
    #
    @21
    cr
    wcel
    #
    @84
    @85
    wi
    @83
    0red
    @80
    @86
    @72
    @39
    zre
    adantr
    @72
    @87
    @80
    @72
    @3
    c2
    @3
    nn0re
    c2
    cr
    wcel
    @72
    2re
    a1i
    resubcld
    #
    adantl
    cc0
    @39
    @21
    lelttr
    syl3anc
    @72
    @85
    @77
    wi
    @80
    @72
    @85
    @77
    @72
    @85
    wa
    #
    @77
    @21
    cn
    wcel
    #
    @89
    @21
    cz
    wcel
    #
    @85
    wa
    @90
    @72
    @91
    @85
    @72
    @3
    c2
    @3
    nn0z
    #
    c2
    cz
    wcel
    @72
    2z
    a1i
    zsubcld
    anim1i
    @21
    elnnz
    sylibr
    @72
    @77
    @90
    wb
    @85
    @72
    @18
    @21
    cn
    @72
    @18
    @16
    c1
    cmin
    co
    #
    @21
    @72
    @17
    @16
    c1
    cmin
    @72
    @16
    @72
    @3
    cc
    wcel
    @16
    cc
    wcel
    @3
    nn0cn
    #
    @3
    peano2cnm
    syl
    subid1d
    #
    oveq1d
    @72
    @93
    @3
    c1
    c1
    caddc
    co
    #
    cmin
    co
    #
    @21
    @72
    @3
    c1
    c1
    @94
    @72
    1cnd
    #
    @98
    subsub4d
    #
    @72
    @96
    c2
    @3
    cmin
    @96
    c2
    wceq
    @72
    1p1e2
    a1i
    oveq2d
    eqtrd
    #
    eqtrd
    eleq1d
    adantr
    mpbird
    ex
    adantl
    syld
    exp4b
    com23
    imp
    sylbi
    imp
    com12
    adantr
    impcom
    @76
    @75
    @78
    @40
    @75
    @78
    wi
    @4
    @75
    @40
    @78
    @75
    @21
    @18
    @39
    clt
    @72
    @21
    @18
    wceq
    @66
    @72
    @21
    @97
    @93
    @18
    @72
    c2
    @96
    @3
    cmin
    c2
    @96
    wceq
    @72
    df-2
    a1i
    oveq2d
    @99
    @72
    @16
    @17
    c1
    cmin
    @72
    @17
    @16
    @95
    eqcomd
    oveq1d
    3eqtr2d
    adantl
    breq2d
    biimpcd
    adantr
    impcom
    @39
    @18
    elfzo0
    syl3anbrc
    exp32
    a1d
    com24
    ex
    com25
    imp
    3adant2
    com14
    syl
    imp
    3adant1
    syl7bi
    com13
    imp31
    @9
    @39
    wceq
    #
    @15
    @60
    wb
    @64
    @101
    @13
    @44
    @14
    @101
    @10
    @41
    @12
    @43
    @9
    @39
    cP
    fveq2
    @101
    @11
    @42
    cP
    @9
    @39
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    adantl
    rspcdv
    ex
    com13
    ad2antrl
    impcom
    expdimp
    impcom
    @0
    @14
    @44
    cE
    f1ocnvdm
    syl2anc
    jca
    orcd
    @54
    @51
    wa
    #
    @56
    @53
    @102
    @54
    @55
    @54
    @51
    simpl
    @102
    @59
    @47
    @14
    wcel
    #
    @55
    @37
    @59
    @54
    @50
    @61
    ad2antrl
    @51
    @54
    @103
    @5
    @26
    @50
    @54
    @103
    wi
    #
    @26
    @5
    @50
    @104
    wi
    #
    @25
    @5
    @105
    wi
    #
    @8
    @24
    @106
    @20
    @54
    @5
    @50
    @24
    @103
    @5
    @54
    @50
    @24
    @103
    wi
    #
    wi
    @5
    @54
    @50
    @107
    @5
    @54
    @50
    wa
    #
    wa
    #
    @24
    @103
    @109
    @23
    @47
    @14
    @109
    @22
    @41
    @7
    @109
    @21
    @39
    cP
    @5
    @108
    @21
    @39
    wceq
    #
    @2
    @1
    @108
    @110
    wi
    @4
    @2
    @72
    @108
    @110
    @73
    @50
    @54
    @72
    @110
    wi
    #
    @50
    @69
    @54
    @111
    wi
    #
    @70
    @66
    @68
    @112
    @67
    @66
    @68
    wa
    #
    @72
    @54
    @110
    @113
    @72
    @54
    @110
    @113
    @72
    wa
    #
    @54
    wa
    #
    @110
    @21
    @39
    clt
    wbr
    wn
    #
    @54
    wa
    #
    @114
    @116
    @54
    @114
    @39
    @21
    cle
    wbr
    #
    @116
    @113
    @72
    @118
    @66
    @72
    @68
    @118
    @75
    @68
    @39
    @93
    cle
    wbr
    #
    @118
    @75
    @80
    @16
    cz
    wcel
    #
    wa
    @68
    @119
    wb
    @66
    @80
    @72
    @120
    @39
    nn0z
    @72
    @3
    cz
    wcel
    #
    @120
    @92
    @3
    peano2zm
    syl
    anim12i
    @39
    @16
    zltlem1
    syl
    @75
    @119
    @118
    @75
    @93
    @21
    @39
    cle
    @72
    @93
    @21
    wceq
    @66
    @100
    adantl
    breq2d
    biimpd
    sylbid
    impancom
    imp
    @114
    @86
    @87
    wa
    @118
    @116
    wb
    @113
    @86
    @72
    @87
    @66
    @86
    @68
    @39
    nn0re
    adantr
    @88
    anim12i
    #
    @39
    @21
    lenlt
    syl
    mpbid
    anim1i
    @115
    @87
    @86
    wa
    #
    @110
    @117
    wb
    @114
    @123
    @54
    @114
    @86
    @87
    @122
    ancomd
    adantr
    @21
    @39
    lttri3
    syl
    mpbird
    exp31
    com23
    3adant2
    sylbi
    impcom
    syl5com
    3ad2ant2
    imp
    fveq2d
    preq1d
    eleq1d
    biimpd
    exp32
    com12
    com14
    adantl
    adantl
    com12
    imp31
    impcom
    @0
    @14
    @47
    cE
    f1ocnvdm
    syl2anc
    jca
    olcd
    pm2.61ian
    @40
    @46
    @48
    @0
    ifel
    sylibr
    clwlkclwwlklem2.f
    fmptd
    @0
    @16
    cF
    iswrdi
    syl
    @5
    @30
    @26
    @2
    @4
    @30
    @1
    @2
    @4
    wa
    #
    cc0
    @3
    cfzo
    co
    #
    cV
    cP
    wf
    #
    @30
    @2
    @126
    @4
    cV
    cP
    wrdf
    adantr
    @124
    @125
    @29
    cV
    cP
    @2
    @4
    @28
    @16
    wceq
    #
    @125
    @29
    wceq
    vx
    cP
    cE
    cF
    cV
    clwlkclwwlklem2.f
    clwlkclwwlklem2a2
    #
    @2
    @127
    @125
    cc0
    @16
    cfz
    co
    #
    @29
    @2
    @72
    @121
    @125
    @129
    wceq
    @73
    @92
    cc0
    @3
    fzoval
    3syl
    @129
    @29
    wceq
    @16
    @28
    @16
    @28
    cc0
    cfz
    oveq2
    eqcoms
    sylan9eq
    syldan
    feq2d
    mpbid
    3adant1
    adantr
    @37
    @15
    vi
    @38
    wral
    #
    @33
    @5
    @26
    @130
    @2
    @4
    @26
    @130
    wi
    @1
    cP
    vi
    cE
    cV
    clwlkclwwlklem2a1
    3adant1
    imp
    @5
    @8
    @130
    @33
    wi
    #
    @25
    @127
    @5
    @8
    wa
    #
    @131
    @5
    @127
    @8
    @2
    @4
    @127
    @1
    @128
    3adant1
    adantr
    @132
    @131
    @127
    @130
    @31
    vi
    @38
    wral
    #
    wi
    @132
    @15
    @31
    vi
    @38
    @5
    @8
    @9
    @38
    wcel
    @15
    @31
    wi
    vx
    cP
    cR
    cE
    cF
    @9
    cV
    clwlkclwwlklem2.f
    clwlkclwwlklem2a4
    impl
    ralimdva
    @127
    @33
    @133
    @130
    @127
    @31
    vi
    @32
    @38
    @28
    @16
    cc0
    cfzo
    oveq2
    raleqdv
    imbi2d
    syl5ibr
    mpcom
    adantrr
    mpd
    3jca
    @26
    @5
    @36
    @8
    @5
    @36
    wi
    #
    @25
    @134
    @7
    @6
    @5
    @7
    @6
    wceq
    @36
    @5
    @6
    @35
    @7
    @5
    @35
    @6
    @2
    @4
    @35
    @6
    wceq
    @1
    vx
    cP
    cE
    cF
    cV
    clwlkclwwlklem2.f
    clwlkclwwlklem2a3
    3adant1
    eqcomd
    eqeq2d
    biimpcd
    eqcoms
    adantr
    impcom
    jca
    ex
end
