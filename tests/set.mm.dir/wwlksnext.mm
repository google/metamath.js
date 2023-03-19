include "cwwlksn.mm"
include "co.mm"
include "wcel.mm"
include "clsw.mm"
include "cfv.mm"
include "cpr.mm"
include "cs1.mm"
include "cconcat.mm"
include "c1.mm"
include "caddc.mm"
include "cvv.mm"
include "cn0.mm"
include "cword.mm"
include "w3a.mm"
include "wa.mm"
include "wi.mm"
include "wwlknbp.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cc0.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "wceq.mm"
include "wwlknp.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "simp1.mm"
include "simprl.mm"
include "cats1un.mm"
include "syl2an.mm"
include "wn.mm"
include "opex.mm"
include "snnz.mm"
include "neii.mm"
include "intnan.mm"
include "df-ne.mm"
include "un00.mm"
include "xchbinxr.mm"
include "mpbir.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "s1cl.mm"
include "ad2antrl.mm"
include "ccatcl.mm"
include "simplrl.mm"
include "simpll.mm"
include "adantr.mm"
include "fzossfzop1.mm"
include "sseld.mm"
include "ad2antlr.mm"
include "imp.mm"
include "wb.mm"
include "oveq2.mm"
include "eleq2d.mm"
include "adantl.mm"
include "mpbird.mm"
include "ccats1val1.mm"
include "syl3anc.mm"
include "eqcomd.mm"
include "fzonn0p1p1.mm"
include "eleqtrrd.mm"
include "preq12d.mm"
include "exp41.mm"
include "impcom.mm"
include "eleq1d.mm"
include "ralbidva.mm"
include "biimpd.mm"
include "ex.mm"
include "com23.mm"
include "3impia.mm"
include "oveq1.mm"
include "ad2antll.mm"
include "cc.mm"
include "nn0cn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "lsw.mm"
include "fzonn0p1.mm"
include "3eqtr4d.mm"
include "simpr.mm"
include "ccats1val2.mm"
include "biimpcd.mm"
include "exp4c.mm"
include "com12.mm"
include "3adant3.mm"
include "fveq2.mm"
include "ralsng.mm"
include "ralunb.mm"
include "sylanbrc.mm"
include "cfz.mm"
include "cuz.mm"
include "elnn0uz.mm"
include "eluzfz2.mm"
include "sylbi.mm"
include "fzelp1.mm"
include "fzosplit.mm"
include "3syl.mm"
include "cz.mm"
include "nn0z.mm"
include "fzosn.mm"
include "syl.mm"
include "uneq2d.mm"
include "raleqdv.mm"
include "ccatlen.mm"
include "oveq1d.mm"
include "simpl2.mm"
include "s1len.mm"
include "oveq12d.mm"
include "peano2nn0.mm"
include "nn0cnd.mm"
include "3eqtrd.mm"
include "oveq2d.mm"
include "3jca.mm"
include "jca.mm"
include "expd.mm"
include "cwwlks.mm"
include "iswwlksn.mm"
include "iswwlks.mm"
include "anbi1i.mm"
include "syl6bb.mm"
include "sylibrd.mm"
include "mpcom.mm"
include "3impib.mm"

theorem wwlksnext
  let cS: class S
  let cT: class T
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let vi: setvar i
  let cW: class W
  assume wwlksnext.v: |- V = ( Vtx ` G )
  assume wwlksnext.e: |- E = ( Edg ` G )


  assert |- ( ( T e. ( N WWalksN G ) /\ S e. V /\ { ( lastS ` T ) , S } e. E ) -> ( T ++ <" S "> ) e. ( ( N + 1 ) WWalksN G ) )

  proof
    cT
    cN
    cG
    cwwlksn
    co
    wcel
    #
    cS
    cV
    wcel
    #
    cT
    clsw
    cfv
    #
    cS
    cpr
    #
    cE
    wcel
    #
    cT
    cS
    cs1
    #
    cconcat
    co
    #
    cN
    c1
    caddc
    co
    #
    cG
    cwwlksn
    co
    wcel
    #
    cG
    cvv
    wcel
    #
    cN
    cn0
    wcel
    #
    cT
    cV
    cword
    #
    wcel
    #
    w3a
    @0
    @1
    @4
    wa
    #
    @8
    wi
    #
    cG
    cN
    cV
    cT
    wwlksnext.v
    wwlknbp
    @9
    @10
    @0
    @14
    wi
    @12
    @9
    @10
    wa
    #
    @0
    @14
    @15
    @0
    wa
    @13
    @6
    c0
    wne
    #
    @6
    @11
    wcel
    #
    vi
    cv
    #
    @6
    cfv
    #
    @18
    c1
    caddc
    co
    #
    @6
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    vi
    cc0
    @6
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
    @24
    @7
    c1
    caddc
    co
    #
    wceq
    #
    wa
    #
    @8
    @15
    @0
    @13
    @31
    wi
    #
    @10
    @0
    @32
    wi
    @9
    @0
    @10
    @32
    @0
    @10
    @13
    @31
    @0
    @12
    cT
    chash
    cfv
    #
    @7
    wceq
    #
    @18
    cT
    cfv
    #
    @20
    cT
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
    @10
    @13
    wa
    #
    @31
    wi
    vi
    cE
    cG
    cN
    cV
    cT
    wwlksnext.v
    wwlksnext.e
    wwlknp
    @41
    @42
    @31
    @41
    @42
    wa
    #
    @28
    @30
    @43
    @16
    @17
    @27
    @43
    @6
    cT
    @33
    cS
    cop
    #
    csn
    #
    cun
    #
    c0
    @41
    @12
    @1
    @6
    @46
    wceq
    @42
    @12
    @34
    @40
    simp1
    #
    @10
    @1
    @4
    simprl
    cT
    cS
    cV
    cats1un
    syl2an
    @46
    c0
    wne
    #
    @43
    @48
    cT
    c0
    wceq
    #
    @45
    c0
    wceq
    #
    wa
    #
    wn
    @50
    @49
    @45
    c0
    @44
    @33
    cS
    opex
    snnz
    neii
    intnan
    @48
    @46
    c0
    wceq
    @51
    @46
    c0
    df-ne
    cT
    @45
    un00
    xchbinxr
    mpbir
    a1i
    eqnetrd
    @41
    @12
    @5
    @11
    wcel
    #
    @17
    @42
    @47
    @1
    @52
    @10
    @4
    cS
    cV
    s1cl
    ad2antrl
    #
    cV
    cT
    @5
    ccatcl
    syl2an
    @43
    @27
    @23
    vi
    cc0
    @7
    cfzo
    co
    #
    wral
    #
    @43
    @55
    @23
    vi
    @39
    cN
    csn
    #
    cun
    #
    wral
    #
    @43
    @23
    vi
    @39
    wral
    #
    @23
    vi
    @56
    wral
    #
    @58
    @41
    @42
    @59
    @12
    @34
    @40
    @42
    @59
    wi
    @12
    @34
    wa
    #
    @42
    @40
    @59
    @61
    @42
    @40
    @59
    wi
    @61
    @42
    wa
    #
    @40
    @59
    @62
    @38
    @23
    vi
    @39
    @62
    @18
    @39
    wcel
    #
    wa
    @37
    @22
    cE
    @62
    @63
    @37
    @22
    wceq
    #
    @42
    @61
    @63
    @64
    wi
    #
    @13
    @10
    @61
    @65
    wi
    #
    @1
    @10
    @66
    wi
    @4
    @1
    @10
    @61
    @63
    @64
    @1
    @10
    wa
    #
    @61
    wa
    #
    @63
    wa
    #
    @35
    @19
    @36
    @21
    @69
    @19
    @35
    @69
    @12
    @1
    @18
    cc0
    @33
    cfzo
    co
    #
    wcel
    #
    @19
    @35
    wceq
    @67
    @12
    @34
    @63
    simplrl
    #
    @68
    @1
    @63
    @1
    @10
    @61
    simpll
    #
    adantr
    #
    @69
    @71
    @18
    @54
    wcel
    #
    @68
    @63
    @75
    @10
    @63
    @75
    wi
    @1
    @61
    @10
    @39
    @54
    @18
    cN
    fzossfzop1
    sseld
    ad2antlr
    imp
    @61
    @71
    @75
    wb
    #
    @67
    @63
    @34
    @76
    @12
    @34
    @70
    @54
    @18
    @33
    @7
    cc0
    cfzo
    oveq2
    #
    eleq2d
    adantl
    ad2antlr
    mpbird
    cS
    @18
    cV
    cT
    ccats1val1
    syl3anc
    eqcomd
    @69
    @21
    @36
    @69
    @12
    @1
    @20
    @70
    wcel
    @21
    @36
    wceq
    @72
    @74
    @69
    @20
    @54
    @70
    @63
    @20
    @54
    wcel
    @68
    @18
    cN
    fzonn0p1p1
    adantl
    @61
    @70
    @54
    wceq
    #
    @67
    @63
    @34
    @78
    @12
    @77
    adantl
    ad2antlr
    eleqtrrd
    cS
    @20
    cV
    cT
    ccats1val1
    syl3anc
    eqcomd
    preq12d
    exp41
    adantr
    impcom
    impcom
    imp
    eleq1d
    ralbidva
    biimpd
    ex
    com23
    3impia
    imp
    @43
    @60
    cN
    @6
    cfv
    #
    @7
    @6
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    @41
    @42
    @82
    @12
    @34
    @42
    @82
    wi
    @40
    @42
    @61
    @82
    @13
    @10
    @61
    @82
    wi
    #
    @4
    @1
    @10
    @83
    wi
    @4
    @1
    @10
    @61
    @82
    @68
    @4
    @82
    @68
    @3
    @81
    cE
    @68
    @2
    @79
    cS
    @80
    @68
    @33
    c1
    cmin
    co
    #
    cT
    cfv
    #
    cN
    cT
    cfv
    #
    @2
    @79
    @68
    @84
    cN
    cT
    @68
    @84
    @7
    c1
    cmin
    co
    #
    cN
    @34
    @84
    @87
    wceq
    @67
    @12
    @33
    @7
    c1
    cmin
    oveq1
    ad2antll
    @10
    @87
    cN
    wceq
    #
    @1
    @61
    @10
    cN
    cc
    wcel
    c1
    cc
    wcel
    #
    @88
    cN
    nn0cn
    ax-1cn
    cN
    c1
    pncan
    sylancl
    ad2antlr
    eqtrd
    fveq2d
    @12
    @2
    @85
    wceq
    @67
    @34
    cT
    @11
    lsw
    ad2antrl
    @68
    @12
    @1
    cN
    @70
    wcel
    #
    @79
    @86
    wceq
    @67
    @12
    @34
    simprl
    #
    @73
    @68
    @90
    cN
    @54
    wcel
    #
    @10
    @92
    @1
    @61
    cN
    fzonn0p1
    ad2antlr
    @34
    @90
    @92
    wb
    @67
    @12
    @34
    @70
    @54
    cN
    @77
    eleq2d
    ad2antll
    mpbird
    cS
    cN
    cV
    cT
    ccats1val1
    syl3anc
    3eqtr4d
    @68
    @80
    cS
    @68
    @12
    @1
    @7
    @33
    wceq
    #
    @80
    cS
    wceq
    @91
    @73
    @61
    @93
    @67
    @61
    @33
    @7
    @12
    @34
    simpr
    eqcomd
    adantl
    cS
    @7
    cV
    cT
    ccats1val2
    syl3anc
    eqcomd
    preq12d
    eleq1d
    biimpcd
    exp4c
    impcom
    impcom
    com12
    3adant3
    imp
    @10
    @60
    @82
    wb
    @41
    @13
    @23
    @82
    vi
    cN
    cn0
    @18
    cN
    wceq
    #
    @22
    @81
    cE
    @94
    @19
    @79
    @21
    @80
    @18
    cN
    @6
    fveq2
    @94
    @20
    @7
    @6
    @18
    cN
    c1
    caddc
    oveq1
    fveq2d
    preq12d
    eleq1d
    ralsng
    ad2antrl
    mpbird
    @23
    vi
    @39
    @56
    ralunb
    sylanbrc
    @43
    @23
    vi
    @54
    @57
    @10
    @54
    @57
    wceq
    @41
    @13
    @10
    @54
    @39
    cN
    @7
    cfzo
    co
    #
    cun
    #
    @57
    @10
    cN
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cc0
    @7
    cfz
    co
    wcel
    @54
    @96
    wceq
    @10
    cN
    cc0
    cuz
    cfv
    wcel
    @97
    cN
    elnn0uz
    cc0
    cN
    eluzfz2
    sylbi
    cN
    cc0
    cN
    fzelp1
    cc0
    @7
    cN
    fzosplit
    3syl
    @10
    @95
    @56
    @39
    @10
    cN
    cz
    wcel
    @95
    @56
    wceq
    cN
    nn0z
    cN
    fzosn
    syl
    uneq2d
    eqtrd
    ad2antrl
    raleqdv
    mpbird
    @43
    @23
    vi
    @26
    @54
    @43
    @25
    @7
    cc0
    cfzo
    @43
    @25
    @33
    @5
    chash
    cfv
    #
    caddc
    co
    #
    c1
    cmin
    co
    @29
    c1
    cmin
    co
    #
    @7
    @43
    @24
    @99
    c1
    cmin
    @41
    @12
    @52
    @24
    @99
    wceq
    @42
    @47
    @53
    cV
    cT
    @5
    ccatlen
    syl2an
    #
    oveq1d
    @43
    @99
    @29
    c1
    cmin
    @43
    @33
    @7
    @98
    c1
    caddc
    @12
    @34
    @40
    @42
    simpl2
    @98
    c1
    wceq
    @43
    cS
    s1len
    a1i
    oveq12d
    #
    oveq1d
    @10
    @100
    @7
    wceq
    #
    @41
    @13
    @10
    @7
    cc
    wcel
    @89
    @103
    @10
    @7
    cN
    peano2nn0
    #
    nn0cnd
    ax-1cn
    @7
    c1
    pncan
    sylancl
    ad2antrl
    3eqtrd
    oveq2d
    raleqdv
    mpbird
    3jca
    @43
    @24
    @99
    @29
    @101
    @102
    eqtrd
    jca
    ex
    syl
    expd
    com12
    adantl
    imp
    @15
    @8
    @31
    wb
    @0
    @15
    @8
    @6
    cG
    cwwlks
    cfv
    wcel
    #
    @30
    wa
    #
    @31
    @10
    @8
    @106
    wb
    #
    @9
    @10
    @7
    cn0
    wcel
    @107
    @104
    cG
    @7
    @6
    iswwlksn
    syl
    adantl
    @105
    @28
    @30
    vi
    cE
    cG
    cV
    @6
    wwlksnext.v
    wwlksnext.e
    iswwlks
    anbi1i
    syl6bb
    adantr
    sylibrd
    ex
    3adant3
    mpcom
    3impib
end
