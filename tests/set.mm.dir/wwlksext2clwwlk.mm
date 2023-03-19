include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "clsw.mm"
include "cfv.mm"
include "cpr.mm"
include "cc0.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "c2.mm"
include "caddc.mm"
include "cclwwlkn.mm"
include "wi.mm"
include "cn0.mm"
include "cvtx.mm"
include "cword.mm"
include "chash.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "wwlknbp1.mm"
include "cv.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "eqcomi.mm"
include "wrdeqi.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "adantl.mm"
include "s1cl.mm"
include "ccatcl.mm"
include "syl2an.mm"
include "adantr.mm"
include "wwlknp.mm"
include "csn.mm"
include "cun.mm"
include "simpll.mm"
include "ad2antlr.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "elfzo0.mm"
include "simp1.mm"
include "peano2nn.mm"
include "cr.mm"
include "nn0re.mm"
include "3ad2ant1.mm"
include "nnre.mm"
include "peano2re.mm"
include "syl.mm"
include "simp3.mm"
include "ltp1d.mm"
include "lttrd.mm"
include "syl3anbrc.mm"
include "sylbi.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "ccatval1.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "fzonn0p1p1.mm"
include "ad3antlr.mm"
include "preq12d.mm"
include "ex.mm"
include "expcom.mm"
include "imp.mm"
include "expdcom.mm"
include "3imp1.mm"
include "eleq1d.mm"
include "ralbidva.mm"
include "biimpd.mm"
include "3exp.mm"
include "com34.mm"
include "oveq1.mm"
include "cc.mm"
include "nn0cn.mm"
include "ad2antll.mm"
include "pncan1.mm"
include "eqtr2d.mm"
include "fveq2d.mm"
include "c0.mm"
include "wne.mm"
include "nn0p1gt0.mm"
include "breq2.mm"
include "hashneq0.mm"
include "mpbid.mm"
include "ccatval1lsw.mm"
include "fveq2.mm"
include "eqcoms.mm"
include "ccatws1ls.mm"
include "ad2ant2r.mm"
include "com12.mm"
include "3adant3.mm"
include "biimpa.mm"
include "simprl1.mm"
include "ralsng.mm"
include "ralunb.mm"
include "sylanbrc.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "fzosplitsn.mm"
include "raleqdv.mm"
include "ccatws1len.mm"
include "oveq1d.mm"
include "1cnd.mm"
include "addcld.mm"
include "pncand.mm"
include "eqtrd.mm"
include "a1d.mm"
include "3ad2antl2.mm"
include "oveq2d.mm"
include "exp42.mm"
include "imp31.mm"
include "adantrd.mm"
include "lswccats1.mm"
include "sylan.mm"
include "3ad2ant3.mm"
include "ccatfv0.mm"
include "biimpcd.mm"
include "impcom.mm"
include "3jca.mm"
include "addassd.mm"
include "1p1e2.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "ad4ant23.mm"
include "2nn.mm"
include "nn0nnaddcl.mm"
include "mpan2.mm"
include "isclwwlknx.mm"
include "mpbir2and.mm"
include "exp31.mm"
include "mpdan.mm"

theorem wwlksext2clwwlk
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vi: setvar i
  assume clwwlkext2edg.v: |- V = ( Vtx ` G )
  assume clwwlkext2edg.e: |- E = ( Edg ` G )


  assert |- ( ( W e. ( N WWalksN G ) /\ Z e. V ) -> ( ( { ( lastS ` W ) , Z } e. E /\ { Z , ( W ` 0 ) } e. E ) -> ( W ++ <" Z "> ) e. ( ( N + 2 ) ClWWalksN G ) ) )

  proof
    cW
    cN
    cG
    cwwlksn
    co
    wcel
    #
    cZ
    cV
    wcel
    #
    cW
    clsw
    cfv
    #
    cZ
    cpr
    #
    cE
    wcel
    #
    cZ
    cc0
    cW
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    wa
    #
    cW
    cZ
    cs1
    #
    cconcat
    co
    #
    cN
    c2
    caddc
    co
    #
    cG
    cclwwlkn
    co
    wcel
    #
    wi
    #
    @0
    cN
    cn0
    wcel
    #
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    cW
    chash
    cfv
    #
    cN
    c1
    caddc
    co
    #
    wceq
    #
    w3a
    #
    @1
    @13
    wi
    cG
    cN
    cW
    wwlknbp1
    @0
    @21
    wa
    #
    @1
    @8
    @12
    @22
    @1
    wa
    #
    @8
    wa
    #
    @12
    @10
    cV
    cword
    #
    wcel
    #
    vi
    cv
    #
    @10
    cfv
    #
    @27
    c1
    caddc
    co
    #
    @10
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    vi
    cc0
    @10
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
    @10
    clsw
    cfv
    #
    cc0
    @10
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @33
    @11
    wceq
    #
    @24
    @26
    @36
    @40
    @23
    @26
    @8
    @22
    cW
    @25
    wcel
    #
    @9
    @25
    wcel
    #
    @26
    @1
    @21
    @43
    @0
    @17
    @14
    @43
    @20
    @17
    @43
    @16
    @25
    cW
    @15
    cV
    cV
    @15
    clwwlkext2edg.v
    eqcomi
    wrdeqi
    eleq2i
    biimpi
    3ad2ant2
    #
    adantl
    #
    cZ
    cV
    s1cl
    #
    cV
    cW
    @9
    ccatcl
    syl2an
    adantr
    @23
    @8
    @36
    @23
    @4
    @36
    @7
    @0
    @21
    @1
    @4
    @36
    wi
    #
    @0
    @43
    @20
    @27
    cW
    cfv
    #
    @29
    cW
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    vi
    cc0
    cN
    cfzo
    co
    #
    wral
    #
    w3a
    #
    @21
    @1
    @48
    wi
    wi
    vi
    cE
    cG
    cN
    cV
    cW
    clwwlkext2edg.v
    clwwlkext2edg.e
    wwlknp
    @55
    @21
    @1
    @4
    @36
    @55
    @21
    @1
    wa
    #
    wa
    #
    @4
    wa
    #
    @36
    @32
    vi
    cc0
    @19
    cfzo
    co
    #
    wral
    #
    @58
    @60
    @32
    vi
    @53
    cN
    csn
    #
    cun
    #
    wral
    #
    @58
    @32
    vi
    @53
    wral
    #
    @32
    vi
    @61
    wral
    #
    @63
    @57
    @64
    @4
    @43
    @20
    @54
    @56
    @64
    @43
    @20
    @56
    @54
    @64
    @43
    @20
    @56
    @54
    @64
    wi
    @43
    @20
    @56
    w3a
    #
    @54
    @64
    @66
    @52
    @32
    vi
    @53
    @66
    @27
    @53
    wcel
    #
    wa
    @51
    @31
    cE
    @43
    @20
    @56
    @67
    @51
    @31
    wceq
    #
    @56
    @43
    @20
    @67
    @68
    wi
    #
    @21
    @1
    @43
    @20
    wa
    #
    @69
    wi
    #
    @14
    @17
    @1
    @71
    wi
    @20
    @1
    @14
    @71
    @70
    @1
    @14
    wa
    #
    @69
    @70
    @72
    wa
    #
    @67
    @68
    @73
    @67
    wa
    #
    @49
    @28
    @50
    @30
    @74
    @28
    @49
    @74
    @43
    @44
    @27
    cc0
    @18
    cfzo
    co
    #
    wcel
    #
    @28
    @49
    wceq
    @73
    @43
    @67
    @43
    @20
    @72
    simpll
    #
    adantr
    #
    @72
    @44
    @70
    @67
    @1
    @44
    @14
    @47
    adantr
    #
    ad2antlr
    #
    @74
    @76
    @27
    @59
    wcel
    #
    @67
    @81
    @73
    @67
    @27
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    @27
    cN
    clt
    wbr
    #
    w3a
    #
    @81
    @27
    cN
    elfzo0
    @85
    @82
    @19
    cn
    wcel
    #
    @27
    @19
    clt
    wbr
    @81
    @82
    @83
    @84
    simp1
    @83
    @82
    @86
    @84
    cN
    peano2nn
    3ad2ant2
    @85
    @27
    cN
    @19
    @82
    @83
    @27
    cr
    wcel
    @84
    @27
    nn0re
    3ad2ant1
    @83
    @82
    cN
    cr
    wcel
    #
    @84
    cN
    nnre
    #
    3ad2ant2
    @83
    @82
    @19
    cr
    wcel
    #
    @84
    @83
    @87
    @89
    @88
    cN
    peano2re
    syl
    3ad2ant2
    @82
    @83
    @84
    simp3
    @83
    @82
    cN
    @19
    clt
    wbr
    @84
    @83
    cN
    @88
    ltp1d
    3ad2ant2
    lttrd
    @27
    @19
    elfzo0
    syl3anbrc
    sylbi
    adantl
    @70
    @76
    @81
    wb
    @72
    @67
    @70
    @75
    @59
    @27
    @20
    @75
    @59
    wceq
    @43
    @18
    @19
    cc0
    cfzo
    oveq2
    #
    adantl
    eleq2d
    ad2antrr
    mpbird
    cV
    cW
    @9
    @27
    ccatval1
    syl3anc
    eqcomd
    @74
    @30
    @50
    @74
    @43
    @44
    @29
    @75
    wcel
    #
    @30
    @50
    wceq
    @78
    @80
    @74
    @91
    @29
    @59
    wcel
    #
    @67
    @92
    @73
    @27
    cN
    fzonn0p1p1
    adantl
    @20
    @91
    @92
    wb
    @43
    @72
    @67
    @20
    @75
    @59
    @29
    @90
    eleq2d
    ad3antlr
    mpbird
    cV
    cW
    @9
    @29
    ccatval1
    syl3anc
    eqcomd
    preq12d
    ex
    expcom
    expcom
    3ad2ant1
    imp
    expdcom
    3imp1
    eleq1d
    ralbidva
    biimpd
    3exp
    com34
    3imp1
    adantr
    @58
    @65
    cN
    @10
    cfv
    #
    @19
    @10
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    @57
    @4
    @96
    @57
    @3
    @95
    cE
    @55
    @56
    @3
    @95
    wceq
    #
    @43
    @20
    @56
    @97
    wi
    @54
    @56
    @70
    @97
    @21
    @1
    @70
    @97
    wi
    #
    @14
    @17
    @1
    @98
    wi
    @20
    @1
    @14
    @98
    @70
    @72
    @97
    @73
    @2
    @93
    cZ
    @94
    @73
    @93
    @18
    c1
    cmin
    co
    #
    @10
    cfv
    #
    @2
    @73
    cN
    @99
    @10
    @73
    @99
    @19
    c1
    cmin
    co
    #
    cN
    @20
    @99
    @101
    wceq
    @43
    @72
    @18
    @19
    c1
    cmin
    oveq1
    ad2antlr
    @73
    cN
    cc
    wcel
    #
    @101
    cN
    wceq
    @14
    @102
    @70
    @1
    cN
    nn0cn
    #
    ad2antll
    cN
    pncan1
    syl
    eqtr2d
    fveq2d
    @73
    @43
    @44
    cW
    c0
    wne
    #
    @100
    @2
    wceq
    @77
    @72
    @44
    @70
    @79
    adantl
    @73
    cc0
    @18
    clt
    wbr
    #
    @104
    @73
    @105
    cc0
    @19
    clt
    wbr
    #
    @14
    @106
    @70
    @1
    cN
    nn0p1gt0
    #
    ad2antll
    @20
    @105
    @106
    wb
    #
    @43
    @72
    @18
    @19
    cc0
    clt
    breq2
    #
    ad2antlr
    mpbird
    @43
    @105
    @104
    wb
    @20
    @72
    cW
    @25
    hashneq0
    ad2antrr
    mpbid
    cW
    @9
    cV
    ccatval1lsw
    syl3anc
    eqtr2d
    @73
    @94
    @18
    @10
    cfv
    #
    cZ
    @20
    @94
    @110
    wceq
    #
    @43
    @72
    @111
    @19
    @18
    @19
    @18
    @10
    fveq2
    eqcoms
    ad2antlr
    @43
    @1
    @110
    cZ
    wceq
    @20
    @14
    cV
    cW
    cZ
    ccatws1ls
    ad2ant2r
    eqtr2d
    preq12d
    expcom
    expcom
    3ad2ant1
    imp
    com12
    3adant3
    imp
    eleq1d
    biimpa
    @58
    @14
    @65
    @96
    wb
    @57
    @14
    @4
    @14
    @17
    @20
    @1
    @55
    simprl1
    #
    adantr
    @32
    @96
    vi
    cN
    cn0
    @27
    cN
    wceq
    #
    @31
    @95
    cE
    @113
    @28
    @93
    @30
    @94
    @27
    cN
    @10
    fveq2
    @113
    @29
    @19
    @10
    @27
    cN
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    ralsng
    syl
    mpbird
    @32
    vi
    @53
    @61
    ralunb
    sylanbrc
    @58
    @32
    vi
    @59
    @62
    @58
    cN
    cc0
    cuz
    cfv
    wcel
    #
    @59
    @62
    wceq
    @57
    @114
    @4
    @57
    @14
    @114
    @112
    cN
    elnn0uz
    sylib
    adantr
    cc0
    cN
    fzosplitsn
    syl
    raleqdv
    mpbird
    @58
    @32
    vi
    @35
    @59
    @58
    @34
    @19
    cc0
    cfzo
    @58
    @34
    @18
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    @19
    @58
    @33
    @115
    c1
    cmin
    @55
    @33
    @115
    wceq
    #
    @56
    @4
    @43
    @20
    @117
    @54
    cV
    cW
    cZ
    ccatws1len
    #
    3ad2ant1
    ad2antrr
    oveq1d
    @57
    @4
    @116
    @19
    wceq
    #
    @20
    @43
    @56
    @4
    @119
    wi
    @54
    @20
    @56
    wa
    #
    @119
    @4
    @120
    @116
    @19
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    @19
    @20
    @116
    @122
    wceq
    @56
    @20
    @115
    @121
    c1
    cmin
    @18
    @19
    c1
    caddc
    oveq1
    #
    oveq1d
    adantr
    @120
    @19
    c1
    @120
    cN
    c1
    @56
    @102
    @20
    @21
    @102
    @1
    @14
    @17
    @102
    @20
    @103
    3ad2ant1
    adantr
    adantl
    @120
    1cnd
    #
    addcld
    @124
    pncand
    eqtrd
    a1d
    3ad2antl2
    imp
    eqtrd
    oveq2d
    raleqdv
    mpbird
    exp42
    syl
    imp31
    adantrd
    imp
    @8
    @23
    @40
    @7
    @23
    @40
    wi
    @4
    @23
    @7
    @40
    @23
    @6
    @39
    cE
    @23
    cZ
    @37
    @5
    @38
    @23
    @37
    cZ
    @22
    @43
    @1
    @37
    cZ
    wceq
    @46
    cZ
    cV
    cW
    lswccats1
    sylan
    eqcomd
    @23
    @43
    @44
    @105
    @5
    @38
    wceq
    @21
    @43
    @0
    @1
    @45
    ad2antlr
    @1
    @44
    @22
    @47
    adantl
    @21
    @105
    @0
    @1
    @21
    @105
    @106
    @14
    @17
    @106
    @20
    @107
    3ad2ant1
    @20
    @14
    @108
    @17
    @109
    3ad2ant3
    mpbird
    ad2antlr
    @43
    @44
    @105
    w3a
    @38
    @5
    cW
    @9
    cV
    ccatfv0
    eqcomd
    syl3anc
    preq12d
    eleq1d
    biimpcd
    adantl
    impcom
    3jca
    @21
    @1
    @42
    @0
    @8
    @56
    @33
    @115
    @11
    @21
    @117
    @1
    @21
    @43
    @117
    @45
    @118
    syl
    adantr
    @21
    @115
    @11
    wceq
    @1
    @21
    @115
    @121
    @11
    @20
    @14
    @115
    @121
    wceq
    @17
    @123
    3ad2ant3
    @14
    @17
    @121
    @11
    wceq
    @20
    @14
    @121
    cN
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @11
    @14
    cN
    c1
    c1
    @103
    @14
    1cnd
    #
    @126
    addassd
    @125
    c2
    cN
    caddc
    1p1e2
    oveq2i
    syl6eq
    3ad2ant1
    eqtrd
    adantr
    eqtrd
    ad4ant23
    @21
    @12
    @41
    @42
    wa
    wb
    #
    @0
    @1
    @8
    @21
    @11
    cn
    wcel
    #
    @127
    @14
    @17
    @128
    @20
    @14
    c2
    cn
    wcel
    @128
    2nn
    cN
    c2
    nn0nnaddcl
    mpan2
    3ad2ant1
    vi
    cE
    cG
    @11
    cV
    @10
    clwwlkext2edg.v
    clwwlkext2edg.e
    isclwwlknx
    syl
    ad3antlr
    mpbir2and
    exp31
    mpdan
    imp
end
