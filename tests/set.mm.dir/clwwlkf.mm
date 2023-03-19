include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "cclwwlkn.mm"
include "cwwlksn.mm"
include "clsw.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "fveq2.mm"
include "fveq1.mm"
include "eqeq12d.mm"
include "elrab2.mm"
include "cvtx.mm"
include "cword.mm"
include "c1.mm"
include "caddc.mm"
include "cpr.mm"
include "cedg.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "w3a.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "cwwlks.mm"
include "cn0.mm"
include "wb.mm"
include "nnnn0.mm"
include "iswwlksn.mm"
include "syl.mm"
include "eqid.mm"
include "iswwlks.mm"
include "a1i.mm"
include "anbi1d.mm"
include "bitrd.mm"
include "cfz.mm"
include "simpll.mm"
include "cle.mm"
include "wbr.mm"
include "peano2nn0.mm"
include "nnre.mm"
include "lep1d.mm"
include "elfz2nn0.mm"
include "syl3anbrc.mm"
include "adantl.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "adantr.mm"
include "mpbird.mm"
include "jca.mm"
include "swrd0len.mm"
include "ex.mm"
include "3ad2antl2.mm"
include "impcom.mm"
include "swrdcl.mm"
include "3ad2ant2.mm"
include "ad2antrl.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "nncn.mm"
include "1cnd.mm"
include "pncand.mm"
include "sylan9eqr.mm"
include "raleqdv.mm"
include "wss.mm"
include "cuz.mm"
include "cz.mm"
include "nnz.mm"
include "peano2zm.mm"
include "lem1d.mm"
include "eluz2.mm"
include "fzoss2.mm"
include "ssralv.mm"
include "simplr.mm"
include "ad2antrr.mm"
include "sseld.mm"
include "imp.mm"
include "swrd0fv.mm"
include "eqcomd.mm"
include "syl3anc.mm"
include "elfzom1elp1fzo.mm"
include "sylan.mm"
include "preq12d.mm"
include "eleq1d.mm"
include "ralbidva.mm"
include "biimpd.mm"
include "com23.mm"
include "syld.mm"
include "sylbid.mm"
include "com14.mm"
include "3adant1.mm"
include "simprl2.mm"
include "ancli.mm"
include "peano2zd.mm"
include "fznn.mm"
include "swrd0fvlsw.mm"
include "swrd0fv0.mm"
include "eqcom.mm"
include "biimpi.mm"
include "lsw.mm"
include "fveq2d.mm"
include "3eqtrd.mm"
include "preq2d.mm"
include "sylan9eq.mm"
include "fzo0end.mm"
include "rspcva.mm"
include "npcand.mm"
include "mpd.mm"
include "com3r.mm"
include "3ad2ant3.mm"
include "eqeltrd.mm"
include "3jca.mm"
include "simpl.mm"
include "mpancom.mm"
include "exp31.mm"
include "imp32.mm"
include "isclwwlknx.mm"
include "sylan2b.mm"
include "fmptd.mm"

theorem clwwlkf
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cF: class F
  let cG: class G
  let cN: class N
  let vi: setvar i
  let cP: class P
  assume clwwlkbij.d: |- D = { w e. ( N WWalksN G ) | ( lastS ` w ) = ( w ` 0 ) }
  assume clwwlkbij.f: |- F = ( t e. D |-> ( t substr <. 0 , N >. ) )

  disjoint G w
  disjoint N w
  disjoint D t
  disjoint G t
  disjoint t w
  disjoint N t
  disjoint G i
  disjoint N i
  disjoint P i
  disjoint P w
  disjoint i t
  assert |- ( N e. NN -> F : D --> ( N ClWWalksN G ) )

  proof
    cN
    cn
    wcel
    #
    vt
    cD
    vt
    cv
    #
    cc0
    cN
    cop
    csubstr
    co
    #
    cN
    cG
    cclwwlkn
    co
    #
    cF
    @1
    cD
    wcel
    @0
    @1
    cN
    cG
    cwwlksn
    co
    #
    wcel
    #
    @1
    clsw
    cfv
    #
    cc0
    @1
    cfv
    #
    wceq
    #
    wa
    #
    @2
    @3
    wcel
    #
    vw
    cv
    #
    clsw
    cfv
    #
    cc0
    @11
    cfv
    #
    wceq
    @8
    vw
    @1
    @4
    cD
    @11
    @1
    wceq
    @12
    @6
    @13
    @7
    @11
    @1
    clsw
    fveq2
    cc0
    @11
    @1
    fveq1
    eqeq12d
    clwwlkbij.d
    elrab2
    @0
    @9
    wa
    @10
    @2
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    vi
    cv
    #
    @2
    cfv
    #
    @17
    c1
    caddc
    co
    #
    @2
    cfv
    #
    cpr
    #
    cG
    cedg
    cfv
    #
    wcel
    #
    vi
    cc0
    @2
    chash
    cfv
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
    @2
    clsw
    cfv
    #
    cc0
    @2
    cfv
    #
    cpr
    #
    @22
    wcel
    #
    w3a
    #
    @24
    cN
    wceq
    #
    wa
    #
    @0
    @5
    @8
    @34
    @0
    @5
    @1
    c0
    wne
    #
    @1
    @15
    wcel
    #
    @17
    @1
    cfv
    #
    @19
    @1
    cfv
    #
    cpr
    #
    @22
    wcel
    #
    vi
    cc0
    @1
    chash
    cfv
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
    w3a
    #
    @41
    cN
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    @8
    @34
    wi
    @0
    @5
    @1
    cG
    cwwlks
    cfv
    wcel
    #
    @47
    wa
    #
    @48
    @0
    cN
    cn0
    wcel
    #
    @5
    @50
    wb
    cN
    nnnn0
    #
    cG
    cN
    @1
    iswwlksn
    syl
    @0
    @49
    @45
    @47
    @49
    @45
    wb
    @0
    vi
    @22
    cG
    @14
    @1
    @14
    eqid
    #
    @22
    eqid
    #
    iswwlks
    a1i
    anbi1d
    bitrd
    @0
    @48
    @8
    @34
    @33
    @0
    @48
    wa
    #
    @8
    wa
    #
    @34
    @55
    @33
    @8
    @48
    @0
    @33
    @36
    @35
    @47
    @0
    @33
    wi
    @44
    @36
    @47
    wa
    #
    @0
    @33
    @57
    @0
    wa
    #
    @36
    cN
    cc0
    @41
    cfz
    co
    #
    wcel
    #
    wa
    @33
    @58
    @36
    @60
    @36
    @47
    @0
    simpll
    @58
    @60
    cN
    cc0
    @46
    cfz
    co
    #
    wcel
    #
    @0
    @62
    @57
    @0
    @51
    @46
    cn0
    wcel
    #
    cN
    @46
    cle
    wbr
    #
    @62
    @52
    @0
    @51
    @63
    @52
    cN
    peano2nn0
    syl
    @0
    cN
    cN
    nnre
    #
    lep1d
    #
    cN
    @46
    elfz2nn0
    syl3anbrc
    #
    adantl
    @57
    @60
    @62
    wb
    #
    @0
    @47
    @68
    @36
    @47
    @59
    @61
    cN
    @41
    @46
    cc0
    cfz
    oveq2
    eleq2d
    #
    adantl
    adantr
    mpbird
    jca
    @14
    @1
    cN
    swrd0len
    syl
    ex
    3ad2antl2
    impcom
    adantr
    @33
    @56
    wa
    #
    @32
    @33
    @70
    @16
    @27
    @31
    @55
    @16
    @33
    @8
    @45
    @16
    @0
    @47
    @36
    @35
    @16
    @44
    @14
    @1
    cc0
    cN
    swrdcl
    3ad2ant2
    ad2antrl
    ad2antrl
    @70
    @27
    @23
    vi
    cc0
    cN
    c1
    cmin
    co
    #
    cfzo
    co
    #
    wral
    #
    @55
    @73
    @33
    @8
    @48
    @0
    @73
    @45
    @47
    @0
    @73
    wi
    #
    @36
    @44
    @47
    @74
    wi
    #
    @35
    @36
    @44
    @75
    @0
    @44
    @47
    @36
    @73
    @0
    @47
    @44
    @36
    @73
    wi
    #
    @0
    @47
    @44
    @76
    wi
    @0
    @47
    wa
    #
    @44
    @40
    vi
    cc0
    cN
    cfzo
    co
    #
    wral
    #
    @76
    @77
    @40
    vi
    @43
    @78
    @47
    @0
    @43
    cc0
    @46
    c1
    cmin
    co
    #
    cfzo
    co
    @78
    @47
    @42
    @80
    cc0
    cfzo
    @41
    @46
    c1
    cmin
    oveq1
    #
    oveq2d
    @0
    @80
    cN
    cc0
    cfzo
    @0
    cN
    c1
    cN
    nncn
    #
    @0
    1cnd
    #
    pncand
    #
    oveq2d
    sylan9eqr
    raleqdv
    @77
    @79
    @40
    vi
    @72
    wral
    #
    @76
    @77
    @72
    @78
    wss
    #
    @79
    @85
    wi
    @0
    @86
    @47
    @0
    cN
    @71
    cuz
    cfv
    wcel
    #
    @86
    @0
    @71
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    @71
    cN
    cle
    wbr
    @87
    @0
    @89
    @88
    cN
    nnz
    #
    cN
    peano2zm
    syl
    @90
    @0
    cN
    @65
    lem1d
    @71
    cN
    eluz2
    syl3anbrc
    @71
    cc0
    cN
    fzoss2
    syl
    #
    adantr
    @40
    vi
    @72
    @78
    ssralv
    syl
    @77
    @36
    @85
    @73
    @77
    @36
    @85
    @73
    wi
    @77
    @36
    wa
    #
    @85
    @73
    @92
    @40
    @23
    vi
    @72
    @92
    @17
    @72
    wcel
    #
    wa
    #
    @39
    @21
    @22
    @94
    @37
    @18
    @38
    @20
    @94
    @36
    @60
    @17
    @78
    wcel
    #
    @37
    @18
    wceq
    @77
    @36
    @93
    simplr
    #
    @77
    @60
    @36
    @93
    @77
    @60
    @62
    @0
    @62
    @47
    @67
    adantr
    @47
    @68
    @0
    @69
    adantl
    mpbird
    ad2antrr
    #
    @92
    @93
    @95
    @0
    @93
    @95
    wi
    @47
    @36
    @0
    @72
    @78
    @17
    @91
    sseld
    ad2antrr
    imp
    @36
    @60
    @95
    w3a
    @18
    @37
    @17
    cN
    @14
    @1
    swrd0fv
    eqcomd
    syl3anc
    @94
    @36
    @60
    @19
    @78
    wcel
    #
    @38
    @20
    wceq
    @96
    @97
    @92
    @89
    @93
    @98
    @0
    @89
    @47
    @36
    @90
    ad2antrr
    @17
    cN
    elfzom1elp1fzo
    sylan
    @36
    @60
    @98
    w3a
    @20
    @38
    @19
    cN
    @14
    @1
    swrd0fv
    eqcomd
    syl3anc
    preq12d
    eleq1d
    ralbidva
    biimpd
    ex
    com23
    syld
    sylbid
    ex
    com23
    com14
    imp
    3adant1
    imp
    impcom
    ad2antrl
    @70
    @23
    vi
    @26
    @72
    @33
    @26
    @72
    wceq
    @56
    @33
    @25
    @71
    cc0
    cfzo
    @24
    cN
    c1
    cmin
    oveq1
    oveq2d
    adantr
    raleqdv
    mpbird
    @56
    @31
    @33
    @56
    @30
    @71
    @1
    cfv
    #
    @7
    cpr
    #
    @22
    @56
    @28
    @99
    @29
    @7
    @56
    @36
    cN
    c1
    @41
    cfz
    co
    #
    wcel
    #
    wa
    #
    @28
    @99
    wceq
    @55
    @103
    @8
    @55
    @36
    @102
    @35
    @36
    @44
    @47
    @0
    simprl2
    @55
    @102
    cN
    c1
    @46
    cfz
    co
    #
    wcel
    #
    @0
    @105
    @48
    @0
    @105
    @0
    @64
    wa
    #
    @0
    @64
    @66
    ancli
    @0
    @46
    cz
    wcel
    @105
    @106
    wb
    @0
    cN
    @90
    peano2zd
    cN
    @46
    fznn
    syl
    mpbird
    adantr
    @48
    @102
    @105
    wb
    #
    @0
    @47
    @107
    @45
    @47
    @101
    @104
    cN
    @41
    @46
    c1
    cfz
    oveq2
    eleq2d
    adantl
    adantl
    mpbird
    jca
    #
    adantr
    cN
    @14
    @1
    swrd0fvlsw
    syl
    @55
    @29
    @7
    wceq
    #
    @8
    @55
    @103
    @109
    @108
    cN
    @14
    @1
    swrd0fv0
    syl
    adantr
    preq12d
    @56
    @100
    @99
    cN
    @1
    cfv
    #
    cpr
    #
    @22
    @56
    @7
    @110
    @99
    @56
    @7
    @6
    @42
    @1
    cfv
    #
    @110
    @8
    @7
    @6
    wceq
    #
    @55
    @8
    @113
    @6
    @7
    eqcom
    biimpi
    adantl
    @55
    @6
    @112
    wceq
    #
    @8
    @45
    @114
    @0
    @47
    @36
    @35
    @114
    @44
    @1
    @15
    lsw
    3ad2ant2
    ad2antrl
    adantr
    @56
    @42
    cN
    @1
    @55
    @42
    cN
    wceq
    @8
    @48
    @0
    @42
    @80
    cN
    @47
    @42
    @80
    wceq
    @45
    @81
    adantl
    @84
    sylan9eqr
    adantr
    fveq2d
    3eqtrd
    preq2d
    @55
    @111
    @22
    wcel
    #
    @8
    @48
    @0
    @115
    @45
    @47
    @0
    @115
    wi
    #
    @44
    @35
    @47
    @116
    wi
    @36
    @47
    @0
    @44
    @115
    @47
    @0
    @44
    @115
    wi
    @47
    @0
    wa
    #
    @44
    @79
    @115
    @117
    @40
    vi
    @43
    @78
    @117
    @42
    cN
    cc0
    cfzo
    @47
    @0
    @42
    @80
    cN
    @81
    @84
    sylan9eq
    oveq2d
    raleqdv
    @0
    @79
    @115
    wi
    @47
    @0
    @79
    @115
    @0
    @79
    wa
    @99
    @71
    c1
    caddc
    co
    #
    @1
    cfv
    #
    cpr
    #
    @22
    wcel
    #
    @115
    @0
    @71
    @78
    wcel
    @79
    @121
    cN
    fzo0end
    @40
    @121
    vi
    @71
    @78
    @17
    @71
    wceq
    #
    @39
    @120
    @22
    @122
    @37
    @99
    @38
    @119
    @17
    @71
    @1
    fveq2
    @122
    @19
    @118
    @1
    @17
    @71
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    rspcva
    sylan
    @0
    @121
    @115
    wi
    @79
    @0
    @121
    @115
    @0
    @120
    @111
    @22
    @0
    @119
    @110
    @99
    @0
    @118
    cN
    @1
    @0
    cN
    c1
    @82
    @83
    npcand
    fveq2d
    preq2d
    eleq1d
    biimpd
    adantr
    mpd
    ex
    adantl
    sylbid
    ex
    com3r
    3ad2ant3
    imp
    impcom
    adantr
    eqeltrd
    eqeltrd
    adantl
    3jca
    @33
    @56
    simpl
    jca
    mpancom
    exp31
    sylbid
    imp32
    @0
    @10
    @34
    wb
    @9
    vi
    @22
    cG
    cN
    @14
    @2
    @53
    @54
    isclwwlknx
    adantr
    mpbird
    sylan2b
    clwwlkbij.f
    fmptd
end
