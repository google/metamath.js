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
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfzo.mm"
include "wa.mm"
include "caddc.mm"
include "cpr.mm"
include "crn.mm"
include "ccnv.mm"
include "wi.mm"
include "fveq2.mm"
include "cn0.mm"
include "lencl.mm"
include "clwlkclwwlklem2fv2.mm"
include "sylan.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "3adant1.mm"
include "ad2antrr.mm"
include "impcom.mm"
include "fveq2d.mm"
include "wf1o.mm"
include "f1f1orn.mm"
include "3ad2ant1.mm"
include "lsw.mm"
include "eqeq1d.mm"
include "cc.mm"
include "nn0cn.mm"
include "id.mm"
include "2cnd.mm"
include "1cnd.mm"
include "subsubd.mm"
include "2m1e1.mm"
include "a1i.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "3syl.mm"
include "adantr.mm"
include "wb.mm"
include "eqeq2.mm"
include "eqcoms.mm"
include "adantl.mm"
include "mpbird.mm"
include "sylbid.mm"
include "3ad2ant2.mm"
include "com12.mm"
include "preq2d.mm"
include "oveq1.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "impancom.mm"
include "f1ocnvfv2.mm"
include "syl2an2.mm"
include "eqcom.mm"
include "biimpi.mm"
include "1e2m1.mm"
include "syl.mm"
include "eqtrd.mm"
include "imp.mm"
include "eqtr4d.mm"
include "exp31.mm"
include "3eqtrd.mm"
include "wn.mm"
include "simpll.mm"
include "cn.mm"
include "clt.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "2cn.mm"
include "subidi.mm"
include "eqeq2d.mm"
include "notbid.mm"
include "anbi12d.mm"
include "csn.mm"
include "elsni.mm"
include "pm2.24d.mm"
include "fzo01.mm"
include "eleq2s.mm"
include "syl6bi.mm"
include "adantld.mm"
include "wne.mm"
include "df-ne.mm"
include "cr.mm"
include "2re.mm"
include "nn0re.mm"
include "simpr.mm"
include "leltned.mm"
include "elfzo0.mm"
include "simp-4l.mm"
include "cz.mm"
include "nn0z.mm"
include "2z.mm"
include "zsubcld.mm"
include "posdifd.mm"
include "biimpa.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "ad5ant24.mm"
include "peano2zm.mm"
include "zltlem1.mm"
include "syl2an.mm"
include "subsub4d.mm"
include "1p1e2.mm"
include "breq2d.mm"
include "bitrd.mm"
include "necom.mm"
include "bitr2i.mm"
include "resubcld.mm"
include "ad2antlr.mm"
include "leltne.mm"
include "bicomd.mm"
include "syl3anc.mm"
include "syl5bi.mm"
include "com23.mm"
include "3jca.mm"
include "exp41.mm"
include "com25.mm"
include "3adant2.mm"
include "sylbi.mm"
include "com13.mm"
include "sylbird.mm"
include "syl5bir.mm"
include "pm2.61i.mm"
include "sylibr.mm"
include "jca.mm"
include "expd.mm"
include "clwlkclwwlklem2fv1.mm"
include "simprr.mm"
include "pm2.61ian.mm"

theorem clwlkclwwlklem2a4
  let vx: setvar x
  let cP: class P
  let cR: class R
  let cE: class E
  let cF: class F
  let cI: class I
  let cV: class V
  assume clwlkclwwlklem2.f: |- F = ( x e. ( 0 ..^ ( ( # ` P ) - 1 ) ) |-> if ( x < ( ( # ` P ) - 2 ) , ( `' E ` { ( P ` x ) , ( P ` ( x + 1 ) ) } ) , ( `' E ` { ( P ` x ) , ( P ` 0 ) } ) ) )

  disjoint P x
  disjoint E x
  disjoint V x
  disjoint I x
  assert |- ( ( E : dom E -1-1-> R /\ P e. Word V /\ 2 <_ ( # ` P ) ) -> ( ( ( lastS ` P ) = ( P ` 0 ) /\ I e. ( 0 ..^ ( ( # ` P ) - 1 ) ) ) -> ( { ( P ` I ) , ( P ` ( I + 1 ) ) } e. ran E -> ( E ` ( F ` I ) ) = { ( P ` I ) , ( P ` ( I + 1 ) ) } ) ) )

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
    #
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
    cI
    cc0
    @4
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wcel
    #
    wa
    #
    cI
    cP
    cfv
    #
    cI
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
    cI
    cF
    cfv
    #
    cE
    cfv
    #
    @17
    wceq
    #
    cI
    @4
    c2
    cmin
    co
    #
    wceq
    #
    @6
    @13
    wa
    #
    @19
    wa
    #
    @22
    @24
    @26
    wa
    #
    @21
    @23
    cP
    cfv
    #
    @8
    cpr
    #
    cE
    ccnv
    #
    cfv
    #
    cE
    cfv
    #
    @29
    @17
    @27
    @20
    @31
    cE
    @26
    @24
    @20
    @31
    wceq
    #
    @6
    @24
    @33
    wi
    #
    @13
    @19
    @3
    @5
    @34
    @1
    @3
    @5
    wa
    #
    @24
    @33
    @24
    @35
    @20
    @23
    cF
    cfv
    #
    @31
    cI
    @23
    cF
    fveq2
    @3
    @4
    cn0
    wcel
    #
    @5
    @36
    @31
    wceq
    cV
    cP
    lencl
    #
    vx
    cP
    cE
    cF
    clwlkclwwlklem2.f
    clwlkclwwlklem2fv2
    sylan
    sylan9eqr
    ex
    3adant1
    ad2antrr
    impcom
    fveq2d
    @26
    @0
    @18
    cE
    wf1o
    #
    @24
    @29
    @18
    wcel
    #
    @32
    @29
    wceq
    @6
    @39
    @13
    @19
    @1
    @3
    @39
    @5
    @0
    cR
    cE
    f1f1orn
    3ad2ant1
    ad2antrr
    #
    @26
    @24
    @40
    @25
    @24
    @19
    @40
    @25
    @24
    wa
    #
    @19
    @40
    @42
    @17
    @29
    @18
    @42
    @17
    @29
    wceq
    #
    @28
    @23
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cpr
    #
    @29
    wceq
    #
    @42
    @45
    @8
    @28
    @25
    @45
    @8
    wceq
    #
    @24
    @13
    @6
    @48
    @9
    @6
    @48
    wi
    @12
    @6
    @9
    @48
    @3
    @1
    @9
    @48
    wi
    @5
    @3
    @9
    @10
    cP
    cfv
    #
    @8
    wceq
    #
    @48
    @3
    @7
    @49
    @8
    cP
    @2
    lsw
    eqeq1d
    #
    @3
    @50
    @48
    @3
    @50
    wa
    #
    @48
    @45
    @49
    wceq
    #
    @52
    @44
    @10
    cP
    @3
    @44
    @10
    wceq
    #
    @50
    @3
    @37
    @4
    cc
    wcel
    #
    @54
    @38
    @4
    nn0cn
    #
    @55
    @4
    c2
    c1
    cmin
    co
    #
    cmin
    co
    #
    @44
    @10
    @55
    @4
    c2
    c1
    @55
    id
    @55
    2cnd
    @55
    1cnd
    subsubd
    @55
    @57
    c1
    @4
    cmin
    @57
    c1
    wceq
    @55
    2m1e1
    a1i
    oveq2d
    eqtr3d
    3syl
    adantr
    fveq2d
    @50
    @48
    @53
    wb
    #
    @3
    @59
    @8
    @49
    @8
    @49
    @45
    eqeq2
    eqcoms
    adantl
    mpbird
    ex
    sylbid
    3ad2ant2
    com12
    adantr
    impcom
    adantr
    preq2d
    @24
    @43
    @47
    wb
    @25
    @24
    @17
    @46
    @29
    @24
    @14
    @28
    @16
    @45
    cI
    @23
    cP
    fveq2
    @24
    @15
    @44
    cP
    cI
    @23
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    #
    eqeq1d
    adantl
    mpbird
    eleq1d
    biimpd
    impancom
    impcom
    @0
    @18
    @29
    cE
    f1ocnvfv2
    syl2an2
    @26
    @24
    @29
    @17
    wceq
    #
    @25
    @24
    @61
    wi
    #
    @19
    @13
    @6
    @62
    @9
    @6
    @62
    wi
    @12
    @6
    @9
    @62
    @3
    @1
    @9
    @62
    wi
    @5
    @3
    @9
    @24
    @61
    @3
    @9
    wa
    #
    @24
    wa
    @29
    @46
    @17
    @63
    @29
    @46
    wceq
    @24
    @63
    @8
    @45
    @28
    @3
    @9
    @8
    @45
    wceq
    #
    @3
    @9
    @50
    @64
    @51
    @3
    @50
    @64
    @50
    @3
    @8
    @49
    @45
    @50
    @8
    @49
    wceq
    @49
    @8
    eqcom
    biimpi
    @3
    @10
    @44
    cP
    @3
    @10
    @58
    @44
    @3
    c1
    @57
    @4
    cmin
    c1
    @57
    wceq
    @3
    1e2m1
    a1i
    oveq2d
    @3
    @4
    c2
    c1
    @3
    @37
    @55
    @38
    @56
    syl
    @3
    2cnd
    @3
    1cnd
    subsubd
    eqtrd
    fveq2d
    sylan9eqr
    ex
    sylbid
    imp
    preq2d
    adantr
    @24
    @17
    @46
    wceq
    @63
    @60
    adantl
    eqtr4d
    exp31
    3ad2ant2
    com12
    adantr
    impcom
    adantr
    impcom
    3eqtrd
    @24
    wn
    #
    @26
    wa
    #
    @21
    @17
    @30
    cfv
    #
    cE
    cfv
    #
    @17
    @66
    @20
    @67
    cE
    @66
    @37
    cI
    cc0
    @23
    cfzo
    co
    wcel
    #
    wa
    #
    @20
    @67
    wceq
    @26
    @65
    @70
    @25
    @65
    @70
    wi
    #
    @19
    @13
    @6
    @71
    @12
    @6
    @71
    wi
    @9
    @6
    @12
    @71
    @6
    @12
    @65
    @70
    @3
    @5
    @12
    @65
    wa
    #
    @70
    wi
    #
    @1
    @3
    @5
    @73
    @3
    @37
    @5
    @73
    wi
    @38
    @37
    @5
    @72
    @70
    @37
    @5
    wa
    #
    @72
    wa
    #
    @37
    @69
    @37
    @5
    @72
    simpll
    @75
    cI
    cn0
    wcel
    #
    @23
    cn
    wcel
    #
    cI
    @23
    clt
    wbr
    #
    w3a
    #
    @69
    @4
    c2
    wceq
    #
    @75
    @79
    wi
    @80
    @72
    @79
    @74
    @80
    @72
    cI
    cc0
    c1
    cfzo
    co
    #
    wcel
    #
    cI
    cc0
    wceq
    #
    wn
    #
    wa
    @79
    @80
    @12
    @82
    @65
    @84
    @80
    @11
    @81
    cI
    @80
    @10
    c1
    cc0
    cfzo
    @80
    @10
    @57
    c1
    @4
    c2
    c1
    cmin
    oveq1
    2m1e1
    syl6eq
    oveq2d
    eleq2d
    @80
    @24
    @83
    @80
    @23
    cc0
    cI
    @80
    @23
    c2
    c2
    cmin
    co
    cc0
    @4
    c2
    c2
    cmin
    oveq1
    c2
    2cn
    subidi
    syl6eq
    eqeq2d
    notbid
    anbi12d
    @82
    @84
    @79
    @84
    @79
    wi
    cI
    cc0
    csn
    #
    @81
    cI
    @85
    wcel
    @83
    @79
    cI
    cc0
    elsni
    pm2.24d
    fzo01
    eleq2s
    imp
    syl6bi
    adantld
    @75
    @80
    wn
    #
    @79
    @74
    @72
    @86
    @79
    wi
    @74
    @86
    @72
    @79
    @86
    @4
    c2
    wne
    #
    @74
    @72
    @79
    wi
    #
    @4
    c2
    df-ne
    @74
    @87
    c2
    @4
    clt
    wbr
    #
    @88
    @74
    c2
    @4
    c2
    cr
    wcel
    #
    @74
    2re
    a1i
    @37
    @4
    cr
    wcel
    @5
    @4
    nn0re
    #
    adantr
    @37
    @5
    simpr
    leltned
    @37
    @89
    @88
    wi
    @5
    @72
    @89
    @37
    @79
    @12
    @65
    @89
    @37
    @79
    wi
    wi
    #
    @12
    @76
    @10
    cn
    wcel
    #
    cI
    @10
    clt
    wbr
    #
    w3a
    @65
    @92
    wi
    #
    cI
    @10
    elfzo0
    @76
    @94
    @95
    @93
    @76
    @94
    @95
    @76
    @37
    @65
    @89
    @94
    @79
    @76
    @37
    @65
    @89
    @94
    @79
    wi
    @76
    @37
    wa
    #
    @65
    wa
    #
    @89
    wa
    #
    @94
    @79
    @98
    @94
    wa
    @76
    @77
    @78
    @76
    @37
    @65
    @89
    @94
    simp-4l
    @37
    @89
    @77
    @76
    @65
    @94
    @37
    @89
    wa
    @23
    cz
    wcel
    #
    cc0
    @23
    clt
    wbr
    #
    @77
    @37
    @99
    @89
    @37
    @4
    c2
    @4
    nn0z
    #
    c2
    cz
    wcel
    @37
    2z
    a1i
    zsubcld
    adantr
    @37
    @89
    @100
    @37
    c2
    @4
    @90
    @37
    2re
    a1i
    #
    @91
    posdifd
    biimpa
    @23
    elnnz
    sylanbrc
    ad5ant24
    @98
    @94
    @78
    @97
    @94
    @78
    wi
    #
    @89
    @96
    @65
    @103
    @96
    @94
    @65
    @78
    @96
    @94
    cI
    @23
    cle
    wbr
    #
    @65
    @78
    wi
    #
    @96
    @94
    cI
    @10
    c1
    cmin
    co
    #
    cle
    wbr
    #
    @104
    @76
    cI
    cz
    wcel
    @10
    cz
    wcel
    #
    @94
    @107
    wb
    @37
    cI
    nn0z
    @37
    @4
    cz
    wcel
    @108
    @101
    @4
    peano2zm
    syl
    cI
    @10
    zltlem1
    syl2an
    @96
    @106
    @23
    cI
    cle
    @96
    @106
    @4
    c1
    c1
    caddc
    co
    #
    cmin
    co
    @23
    @96
    @4
    c1
    c1
    @37
    @55
    @76
    @56
    adantl
    @96
    1cnd
    #
    @110
    subsub4d
    @96
    @109
    c2
    @4
    cmin
    @109
    c2
    wceq
    @96
    1p1e2
    a1i
    oveq2d
    eqtrd
    breq2d
    bitrd
    @96
    @104
    @105
    @65
    @23
    cI
    wne
    #
    @96
    @104
    wa
    #
    @78
    @111
    cI
    @23
    wne
    @65
    @23
    cI
    necom
    cI
    @23
    df-ne
    bitr2i
    @112
    @111
    @78
    @112
    cI
    cr
    wcel
    #
    @23
    cr
    wcel
    #
    @104
    @111
    @78
    wb
    @76
    @113
    @37
    @104
    cI
    nn0re
    ad2antrr
    @37
    @114
    @76
    @104
    @37
    @4
    c2
    @91
    @102
    resubcld
    ad2antlr
    @96
    @104
    simpr
    @113
    @114
    @104
    w3a
    @78
    @111
    cI
    @23
    leltne
    bicomd
    syl3anc
    biimpd
    syl5bi
    ex
    sylbid
    com23
    imp
    adantr
    imp
    3jca
    ex
    exp41
    com25
    imp
    3adant2
    sylbi
    imp
    com13
    adantr
    sylbird
    syl5bir
    com23
    imp
    com12
    pm2.61i
    cI
    @23
    elfzo0
    sylibr
    jca
    exp31
    syl
    imp
    3adant1
    expd
    com12
    adantl
    impcom
    adantr
    impcom
    vx
    cP
    cE
    cF
    cI
    clwlkclwwlklem2.f
    clwlkclwwlklem2fv1
    syl
    fveq2d
    @26
    @39
    @65
    @19
    @68
    @17
    wceq
    @41
    @65
    @25
    @19
    simprr
    @0
    @18
    @17
    cE
    f1ocnvfv2
    syl2an2
    eqtrd
    pm2.61ian
    exp31
end
