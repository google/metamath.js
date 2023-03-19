include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "cn0.mm"
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
include "cvv.mm"
include "cword.mm"
include "w3a.mm"
include "wwlknbp.mm"
include "cv.mm"
include "c1.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "wceq.mm"
include "simp3.mm"
include "adantr.mm"
include "s1cl.mm"
include "ccatcl.mm"
include "syl2an.mm"
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
include "3ad2ant2.mm"
include "cr.mm"
include "nn0re.mm"
include "3ad2ant1.mm"
include "nnre.mm"
include "peano2re.mm"
include "syl.mm"
include "ltp1d.mm"
include "lttrd.mm"
include "syl3anbrc.mm"
include "sylbi.mm"
include "adantl.mm"
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
include "eleq1d.mm"
include "ralbidva.mm"
include "biimpd.mm"
include "ex.mm"
include "com23.mm"
include "3impia.mm"
include "com12.mm"
include "impcom.mm"
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
include "3adantl3.mm"
include "impr.mm"
include "simprlr.mm"
include "ralsng.mm"
include "ralunb.mm"
include "sylanbrc.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "biimpi.mm"
include "fzosplitsn.mm"
include "raleqdv.mm"
include "ccatws1len.mm"
include "oveq1d.mm"
include "ax-1cn.mm"
include "addcl.mm"
include "simpr.mm"
include "pncand.mm"
include "sylancl.mm"
include "sylan9eqr.mm"
include "imp.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "exp32.mm"
include "adantrd.mm"
include "simpl.mm"
include "lswccats1.mm"
include "ccatfv0.mm"
include "exp31.mm"
include "cvtx.mm"
include "wwlknbp2OLD.mm"
include "wrdeqi.mm"
include "eqcomi.mm"
include "eleq2i.mm"
include "anim1i.mm"
include "impel.mm"
include "biimpcd.mm"
include "3jca.mm"
include "1cnd.mm"
include "addassd.mm"
include "1p1e2.mm"
include "oveq2i.mm"
include "syl6eq.mm"
include "sylan9eq.mm"
include "2nn.mm"
include "nn0nnaddcl.mm"
include "mpan2.mm"
include "isclwwlknx.mm"
include "ad3antrrr.mm"
include "mpbir2and.mm"
include "mpancom.mm"
include "3impib.mm"

theorem wwlksext2clwwlkOLD
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let cZ: class Z
  let vi: setvar i
  assume clwwlkext2edg.v: |- V = ( Vtx ` G )
  assume clwwlkext2edg.e: |- E = ( Edg ` G )


  assert |- ( ( W e. ( N WWalksN G ) /\ Z e. V /\ N e. NN0 ) -> ( ( { ( lastS ` W ) , Z } e. E /\ { Z , ( W ` 0 ) } e. E ) -> ( W ++ <" Z "> ) e. ( ( N + 2 ) ClWWalksN G ) ) )

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
    cN
    cn0
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
    cG
    cvv
    wcel
    #
    @2
    cW
    cV
    cword
    #
    wcel
    #
    w3a
    #
    @0
    @1
    @2
    wa
    #
    @14
    wi
    cG
    cN
    cV
    cW
    clwwlkext2edg.v
    wwlknbp
    @18
    @0
    wa
    #
    @19
    @9
    @13
    @20
    @19
    wa
    #
    @9
    wa
    #
    @13
    @11
    @16
    wcel
    #
    vi
    cv
    #
    @11
    cfv
    #
    @24
    c1
    caddc
    co
    #
    @11
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    vi
    cc0
    @11
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
    @11
    clsw
    cfv
    #
    cc0
    @11
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @30
    @12
    wceq
    #
    @22
    @23
    @33
    @37
    @21
    @23
    @9
    @20
    @17
    @10
    @16
    wcel
    #
    @23
    @19
    @18
    @17
    @0
    @15
    @2
    @17
    simp3
    adantr
    @1
    @40
    @2
    cZ
    cV
    s1cl
    adantr
    #
    cV
    cW
    @10
    ccatcl
    syl2an
    adantr
    @21
    @9
    @33
    @21
    @5
    @33
    @8
    @20
    @19
    @5
    @33
    wi
    #
    @0
    @19
    @42
    wi
    #
    @18
    @0
    @17
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
    @24
    cW
    cfv
    #
    @26
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
    @43
    vi
    cE
    cG
    cN
    cV
    cW
    clwwlkext2edg.v
    clwwlkext2edg.e
    wwlknp
    @53
    @19
    @5
    @33
    @53
    @19
    @5
    wa
    #
    wa
    #
    @33
    @29
    vi
    cc0
    @45
    cfzo
    co
    #
    wral
    #
    @55
    @57
    @29
    vi
    @51
    cN
    csn
    #
    cun
    #
    wral
    #
    @55
    @29
    vi
    @51
    wral
    #
    @29
    vi
    @58
    wral
    #
    @60
    @54
    @53
    @61
    @19
    @53
    @61
    wi
    @5
    @53
    @19
    @61
    @17
    @46
    @52
    @19
    @61
    wi
    @17
    @46
    wa
    #
    @19
    @52
    @61
    @63
    @19
    @52
    @61
    wi
    @63
    @19
    wa
    #
    @52
    @61
    @64
    @50
    @29
    vi
    @51
    @64
    @24
    @51
    wcel
    #
    wa
    #
    @49
    @28
    cE
    @66
    @47
    @25
    @48
    @27
    @66
    @25
    @47
    @66
    @17
    @40
    @24
    cc0
    @44
    cfzo
    co
    #
    wcel
    #
    @25
    @47
    wceq
    @64
    @17
    @65
    @17
    @46
    @19
    simpll
    #
    adantr
    #
    @19
    @40
    @63
    @65
    @41
    ad2antlr
    #
    @66
    @68
    @24
    @56
    wcel
    #
    @65
    @72
    @64
    @65
    @24
    cn0
    wcel
    #
    cN
    cn
    wcel
    #
    @24
    cN
    clt
    wbr
    #
    w3a
    #
    @72
    @24
    cN
    elfzo0
    @76
    @73
    @45
    cn
    wcel
    #
    @24
    @45
    clt
    wbr
    @72
    @73
    @74
    @75
    simp1
    @74
    @73
    @77
    @75
    cN
    peano2nn
    3ad2ant2
    @76
    @24
    cN
    @45
    @73
    @74
    @24
    cr
    wcel
    @75
    @24
    nn0re
    3ad2ant1
    @74
    @73
    cN
    cr
    wcel
    #
    @75
    cN
    nnre
    #
    3ad2ant2
    @74
    @73
    @45
    cr
    wcel
    #
    @75
    @74
    @78
    @80
    @79
    cN
    peano2re
    syl
    3ad2ant2
    @73
    @74
    @75
    simp3
    @74
    @73
    cN
    @45
    clt
    wbr
    @75
    @74
    cN
    @79
    ltp1d
    3ad2ant2
    lttrd
    @24
    @45
    elfzo0
    syl3anbrc
    sylbi
    adantl
    @63
    @68
    @72
    wb
    @19
    @65
    @63
    @67
    @56
    @24
    @46
    @67
    @56
    wceq
    @17
    @44
    @45
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
    @10
    @24
    ccatval1
    syl3anc
    eqcomd
    @66
    @27
    @48
    @66
    @17
    @40
    @26
    @67
    wcel
    #
    @27
    @48
    wceq
    @70
    @71
    @66
    @82
    @26
    @56
    wcel
    #
    @65
    @83
    @64
    @24
    cN
    fzonn0p1p1
    adantl
    @46
    @82
    @83
    wb
    @17
    @19
    @65
    @46
    @67
    @56
    @26
    @81
    eleq2d
    ad3antlr
    mpbird
    cV
    cW
    @10
    @26
    ccatval1
    syl3anc
    eqcomd
    preq12d
    eleq1d
    ralbidva
    biimpd
    ex
    com23
    3impia
    com12
    adantr
    impcom
    @55
    @62
    cN
    @11
    cfv
    #
    @45
    @11
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    @53
    @19
    @5
    @87
    @53
    @19
    wa
    #
    @5
    @87
    @88
    @4
    @86
    cE
    @17
    @46
    @19
    @4
    @86
    wceq
    @52
    @64
    @3
    @84
    cZ
    @85
    @64
    @84
    @44
    c1
    cmin
    co
    #
    @11
    cfv
    #
    @3
    @64
    cN
    @89
    @11
    @64
    @89
    @45
    c1
    cmin
    co
    #
    cN
    @46
    @89
    @91
    wceq
    @17
    @19
    @44
    @45
    c1
    cmin
    oveq1
    ad2antlr
    @64
    cN
    cc
    wcel
    #
    @91
    cN
    wceq
    @2
    @92
    @63
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
    @64
    @17
    @40
    cW
    c0
    wne
    #
    @90
    @3
    wceq
    @69
    @19
    @40
    @63
    @41
    adantl
    @64
    cc0
    @44
    clt
    wbr
    #
    @94
    @64
    @95
    cc0
    @45
    clt
    wbr
    #
    @2
    @96
    @63
    @1
    cN
    nn0p1gt0
    #
    ad2antll
    @46
    @95
    @96
    wb
    #
    @17
    @19
    @44
    @45
    cc0
    clt
    breq2
    #
    ad2antlr
    mpbird
    @17
    @95
    @94
    wb
    @46
    @19
    cW
    @16
    hashneq0
    ad2antrr
    mpbid
    cW
    @10
    cV
    ccatval1lsw
    syl3anc
    eqtr2d
    @64
    @85
    @44
    @11
    cfv
    #
    cZ
    @46
    @85
    @100
    wceq
    #
    @17
    @19
    @101
    @45
    @44
    @45
    @44
    @11
    fveq2
    eqcoms
    ad2antlr
    @17
    @1
    @100
    cZ
    wceq
    @46
    @2
    cV
    cW
    cZ
    ccatws1ls
    ad2ant2r
    eqtr2d
    preq12d
    3adantl3
    eleq1d
    biimpd
    impr
    @55
    @2
    @62
    @87
    wb
    @53
    @1
    @2
    @5
    simprlr
    @29
    @87
    vi
    cN
    cn0
    @24
    cN
    wceq
    #
    @28
    @86
    cE
    @102
    @25
    @84
    @27
    @85
    @24
    cN
    @11
    fveq2
    @102
    @26
    @45
    @11
    @24
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
    @29
    vi
    @51
    @58
    ralunb
    sylanbrc
    @55
    @29
    vi
    @56
    @59
    @55
    cN
    cc0
    cuz
    cfv
    wcel
    #
    @56
    @59
    wceq
    @54
    @103
    @53
    @2
    @103
    @1
    @5
    @2
    @103
    cN
    elnn0uz
    biimpi
    ad2antlr
    adantl
    cc0
    cN
    fzosplitsn
    syl
    raleqdv
    mpbird
    @55
    @29
    vi
    @32
    @56
    @55
    @31
    @45
    cc0
    cfzo
    @55
    @31
    @44
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    @45
    @55
    @30
    @104
    c1
    cmin
    @53
    @30
    @104
    wceq
    #
    @54
    @17
    @46
    @106
    @52
    cV
    cW
    cZ
    ccatws1len
    #
    3ad2ant1
    adantr
    oveq1d
    @53
    @54
    @105
    @45
    wceq
    #
    @46
    @17
    @54
    @108
    wi
    @52
    @54
    @46
    @108
    @2
    @46
    @108
    wi
    @1
    @5
    @2
    @46
    @108
    @46
    @2
    @105
    @45
    c1
    caddc
    co
    #
    c1
    cmin
    co
    #
    @45
    @46
    @104
    @109
    c1
    cmin
    @44
    @45
    c1
    caddc
    oveq1
    #
    oveq1d
    @2
    @92
    c1
    cc
    wcel
    #
    @110
    @45
    wceq
    @93
    ax-1cn
    @92
    @112
    wa
    @45
    c1
    cN
    c1
    addcl
    @92
    @112
    simpr
    pncand
    sylancl
    sylan9eqr
    ex
    ad2antlr
    com12
    3ad2ant2
    imp
    eqtrd
    oveq2d
    raleqdv
    mpbird
    exp32
    syl
    adantl
    imp
    adantrd
    imp
    @9
    @21
    @37
    @8
    @21
    @37
    wi
    @5
    @21
    @8
    @37
    @21
    @7
    @36
    cE
    @20
    @19
    @7
    @36
    wceq
    #
    @18
    @63
    @19
    @113
    wi
    #
    @0
    @2
    @15
    @63
    @114
    wi
    @17
    @63
    @2
    @114
    @63
    @2
    @19
    @113
    @63
    @2
    wa
    #
    @19
    wa
    #
    cZ
    @34
    @6
    @35
    @116
    @34
    cZ
    @115
    @17
    @1
    @34
    cZ
    wceq
    @19
    @17
    @46
    @2
    simpll
    #
    @1
    @2
    simpl
    cZ
    cV
    cW
    lswccats1
    syl2an
    eqcomd
    @116
    @17
    @40
    @95
    @6
    @35
    wceq
    @115
    @17
    @19
    @117
    adantr
    @19
    @40
    @115
    @41
    adantl
    @115
    @95
    @19
    @115
    @95
    @96
    @2
    @96
    @63
    @97
    adantl
    @46
    @98
    @17
    @2
    @99
    ad2antlr
    mpbird
    adantr
    @17
    @40
    @95
    w3a
    @35
    @6
    cW
    @10
    cV
    ccatfv0
    eqcomd
    syl3anc
    preq12d
    exp31
    com12
    3ad2ant2
    @0
    cW
    cG
    cvtx
    cfv
    #
    cword
    #
    wcel
    #
    @46
    wa
    @63
    cG
    cN
    cW
    wwlknbp2OLD
    @120
    @17
    @46
    @120
    @17
    @119
    @16
    cW
    @16
    @119
    cV
    @118
    clwwlkext2edg.v
    wrdeqi
    eqcomi
    eleq2i
    biimpi
    anim1i
    syl
    #
    impel
    imp
    eleq1d
    biimpcd
    adantl
    impcom
    3jca
    @21
    @39
    @9
    @20
    @19
    @39
    @0
    @19
    @39
    wi
    #
    @18
    @0
    @63
    @122
    @121
    @63
    @19
    @39
    @64
    @30
    @104
    @12
    @17
    @106
    @46
    @19
    @107
    ad2antrr
    @63
    @19
    @104
    @109
    @12
    @46
    @104
    @109
    wceq
    @17
    @111
    adantl
    @2
    @109
    @12
    wceq
    @1
    @2
    @109
    cN
    c1
    c1
    caddc
    co
    #
    caddc
    co
    @12
    @2
    cN
    c1
    c1
    @93
    @2
    1cnd
    #
    @124
    addassd
    @123
    c2
    cN
    caddc
    1p1e2
    oveq2i
    syl6eq
    adantl
    sylan9eq
    eqtrd
    ex
    syl
    adantl
    imp
    adantr
    @18
    @13
    @38
    @39
    wa
    wb
    #
    @0
    @19
    @9
    @18
    @12
    cn
    wcel
    #
    @125
    @2
    @15
    @126
    @17
    @2
    c2
    cn
    wcel
    @126
    2nn
    cN
    c2
    nn0nnaddcl
    mpan2
    3ad2ant2
    vi
    cE
    cG
    @12
    cV
    @11
    clwwlkext2edg.v
    clwwlkext2edg.e
    isclwwlknx
    syl
    ad3antrrr
    mpbir2and
    exp31
    mpancom
    3impib
end
