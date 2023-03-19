include "crusgr.mm"
include "wbr.mm"
include "cfn.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "cc0.mm"
include "cv.mm"
include "cfv.mm"
include "cwwlksn.mm"
include "crab.mm"
include "chash.mm"
include "c1.mm"
include "caddc.mm"
include "wb.mm"
include "simpr2.mm"
include "simpr3.mm"
include "rusgrnumwwlklem.mm"
include "eqeq1d.mm"
include "syl2anc.mm"
include "cop.mm"
include "csubstr.mm"
include "clsw.mm"
include "cpr.mm"
include "cedg.mm"
include "wrex.mm"
include "csu.mm"
include "wi.mm"
include "eqid.mm"
include "wwlksnredwwlkn0.mm"
include "ex.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "imp.mm"
include "rabbidva.mm"
include "adantr.mm"
include "fveq2d.mm"
include "simp2.mm"
include "pm4.71ri.mm"
include "a1i.mm"
include "rexbidva.mm"
include "fveq1.mm"
include "rexrab.mm"
include "syl6bbr.mm"
include "cvtx.mm"
include "simplr1.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "hashwwlksnext.mm"
include "3syl.mm"
include "cbvrabv.mm"
include "sumeq1i.mm"
include "3eqtrd.mm"
include "rusgrnumwwlkslem.mm"
include "eqcomd.mm"
include "elrabi.mm"
include "wwlksnexthasheq.mm"
include "syl.mm"
include "cusgr.mm"
include "cxnn0.mm"
include "wral.mm"
include "rusgrpropadjvtx.mm"
include "cword.mm"
include "c0.mm"
include "wne.mm"
include "elrab.mm"
include "cfzo.mm"
include "wwlknp.mm"
include "simpll.mm"
include "clt.mm"
include "nn0p1gt0.mm"
include "breq2.mm"
include "ad2antlr.mm"
include "mpbird.mm"
include "wn.mm"
include "cle.mm"
include "hashle00.mm"
include "cr.mm"
include "lencl.mm"
include "nn0red.mm"
include "0re.mm"
include "lenlt.mm"
include "bicomd.mm"
include "sylancl.mm"
include "nne.mm"
include "3bitr4rd.mm"
include "ad2antrr.mm"
include "con4bid.mm"
include "jca.mm"
include "3adant3.mm"
include "sylbi.mm"
include "lswcl.mm"
include "preq1.mm"
include "eleq1d.mm"
include "rabbidv.mm"
include "rspcva.mm"
include "sylancom.mm"
include "exp41.mm"
include "com14.mm"
include "imp41.mm"
include "sumeq2dv.mm"
include "cmul.mm"
include "oveq1.mm"
include "cc.mm"
include "wwlksnfi.mm"
include "3ad2ant1.mm"
include "rabfi.mm"
include "cfusgr.mm"
include "rusgrusgr.mm"
include "simp1.mm"
include "anim12i.mm"
include "isfusgr.mm"
include "sylibr.mm"
include "simpl.mm"
include "ne0i.mm"
include "3ad2ant2.mm"
include "frusgrnn0.mm"
include "syl3anc.mm"
include "nn0cnd.mm"
include "fsumconst.mm"
include "expp1d.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"
include "peano2nn0.mm"
include "sylbid.mm"

theorem rusgrnumwwlks
  let vw: setvar w
  let vv: setvar v
  let cP: class P
  let vn: setvar n
  let cG: class G
  let cK: class K
  let cL: class L
  let cN: class N
  let cV: class V
  let vi: setvar i
  let vp: setvar p
  let vx: setvar x
  let vy: setvar y
  assume rusgrnumwwlk.v: |- V = ( Vtx ` G )
  assume rusgrnumwwlk.l: |- L = ( v e. V , n e. NN0 |-> ( # ` { w e. ( n WWalksN G ) | ( w ` 0 ) = v } ) )

  disjoint G n
  disjoint G v
  disjoint G w
  disjoint n v
  disjoint n w
  disjoint v w
  disjoint N n
  disjoint N v
  disjoint N w
  disjoint P n
  disjoint P v
  disjoint P w
  disjoint V n
  disjoint V v
  disjoint V w
  disjoint K w
  disjoint G i
  disjoint i w
  disjoint N i
  disjoint G p
  disjoint G x
  disjoint G y
  disjoint i n
  disjoint i p
  disjoint i x
  disjoint i y
  disjoint n p
  disjoint n x
  disjoint n y
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint K p
  disjoint K y
  disjoint N x
  disjoint N y
  disjoint P x
  disjoint P y
  disjoint V p
  disjoint V y
  assert |- ( ( G RegUSGraph K /\ ( V e. Fin /\ P e. V /\ N e. NN0 ) ) -> ( ( P L N ) = ( K ^ N ) -> ( P L ( N + 1 ) ) = ( K ^ ( N + 1 ) ) ) )

  proof
    cG
    cK
    crusgr
    wbr
    #
    cV
    cfn
    wcel
    #
    cP
    cV
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    wa
    #
    cP
    cN
    cL
    co
    #
    cK
    cN
    cexp
    co
    #
    wceq
    #
    cc0
    vw
    cv
    #
    cfv
    #
    cP
    wceq
    #
    vw
    cN
    cG
    cwwlksn
    co
    #
    crab
    #
    chash
    cfv
    #
    @7
    wceq
    #
    cP
    cN
    c1
    caddc
    co
    #
    cL
    co
    #
    cK
    @16
    cexp
    co
    #
    wceq
    #
    @5
    @2
    @3
    @8
    @15
    wb
    @0
    @1
    @2
    @3
    simpr2
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    @2
    @3
    wa
    @6
    @14
    @7
    vw
    vv
    cP
    vn
    cG
    cL
    cN
    cV
    rusgrnumwwlk.v
    rusgrnumwwlk.l
    rusgrnumwwlklem
    eqeq1d
    syl2anc
    @5
    @15
    @19
    @5
    @15
    wa
    #
    @19
    @11
    vw
    @16
    cG
    cwwlksn
    co
    #
    crab
    #
    chash
    cfv
    #
    @18
    wceq
    #
    @22
    @25
    @9
    cc0
    @16
    cop
    csubstr
    co
    vy
    cv
    #
    wceq
    #
    cc0
    @27
    cfv
    #
    cP
    wceq
    #
    @27
    clsw
    cfv
    #
    @9
    clsw
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    #
    w3a
    #
    vy
    @12
    wrex
    #
    vw
    @23
    crab
    #
    chash
    cfv
    #
    @13
    @34
    vw
    @23
    crab
    #
    chash
    cfv
    #
    vy
    csu
    #
    @18
    @22
    @24
    @36
    chash
    @5
    @24
    @36
    wceq
    @15
    @5
    @11
    @35
    vw
    @23
    @5
    @9
    @23
    wcel
    #
    @11
    @35
    wb
    #
    @4
    @41
    @42
    wi
    #
    @0
    @3
    @1
    @43
    @2
    @3
    @41
    @42
    vy
    cP
    @32
    cG
    cN
    @9
    @32
    eqid
    #
    wwlksnredwwlkn0
    ex
    3ad2ant3
    adantl
    imp
    rabbidva
    adantr
    fveq2d
    @22
    @37
    @34
    vy
    cc0
    vx
    cv
    #
    cfv
    #
    cP
    wceq
    #
    vx
    @12
    crab
    #
    wrex
    #
    vw
    @23
    crab
    #
    chash
    cfv
    #
    @48
    @39
    vy
    csu
    #
    @40
    @22
    @36
    @50
    chash
    @5
    @36
    @50
    wceq
    @15
    @5
    @35
    @49
    vw
    @23
    @5
    @41
    wa
    #
    @35
    @30
    @34
    wa
    #
    vy
    @12
    wrex
    @49
    @53
    @34
    @54
    vy
    @12
    @34
    @54
    wb
    @53
    @27
    @12
    wcel
    #
    wa
    @34
    @30
    @28
    @30
    @33
    simp2
    pm4.71ri
    a1i
    rexbidva
    @47
    @30
    @34
    vy
    vx
    @12
    @45
    @27
    wceq
    @46
    @29
    cP
    cc0
    @45
    @27
    fveq1
    eqeq1d
    rexrab
    syl6bbr
    rabbidva
    adantr
    fveq2d
    @22
    @1
    cG
    cvtx
    cfv
    #
    cfn
    wcel
    #
    @51
    @52
    wceq
    @1
    @2
    @3
    @0
    @15
    simplr1
    @1
    @57
    cV
    @56
    cfn
    rusgrnumwwlk.v
    eleq1i
    #
    biimpi
    vw
    vy
    vx
    cP
    @32
    cG
    @16
    cN
    @23
    @48
    @23
    eqid
    @44
    @48
    eqid
    hashwwlksnext
    3syl
    @52
    @40
    wceq
    @22
    @48
    @13
    @39
    vy
    @47
    @11
    vx
    vw
    @12
    @45
    @9
    wceq
    @46
    @10
    cP
    cc0
    @45
    @9
    fveq1
    eqeq1d
    cbvrabv
    sumeq1i
    a1i
    3eqtrd
    @22
    @40
    @13
    cK
    vy
    csu
    #
    @18
    @22
    @13
    @39
    cK
    vy
    @22
    @27
    @13
    wcel
    #
    wa
    #
    @39
    @28
    @33
    wa
    vw
    @23
    crab
    #
    chash
    cfv
    #
    @31
    vn
    cv
    #
    cpr
    #
    @32
    wcel
    #
    vn
    cV
    crab
    #
    chash
    cfv
    #
    cK
    @60
    @39
    @63
    wceq
    @22
    @60
    @38
    @62
    chash
    @60
    @62
    @38
    @28
    @33
    vw
    cP
    @23
    @27
    @12
    rusgrnumwwlkslem
    eqcomd
    fveq2d
    adantl
    @61
    @55
    @63
    @68
    wceq
    @60
    @55
    @22
    @11
    vw
    @27
    @12
    elrabi
    adantl
    vw
    vn
    @32
    cG
    cN
    cV
    @27
    rusgrnumwwlk.v
    @44
    wwlksnexthasheq
    syl
    @0
    @4
    @15
    @60
    @68
    cK
    wceq
    #
    @0
    cG
    cusgr
    wcel
    #
    cK
    cxnn0
    wcel
    #
    vp
    cv
    #
    @64
    cpr
    #
    @32
    wcel
    #
    vn
    cV
    crab
    #
    chash
    cfv
    #
    cK
    wceq
    #
    vp
    cV
    wral
    #
    w3a
    @4
    @15
    @60
    @69
    wi
    wi
    wi
    #
    vp
    vn
    cG
    cK
    cV
    rusgrnumwwlk.v
    rusgrpropadjvtx
    @78
    @70
    @79
    @71
    @60
    @4
    @15
    @78
    @69
    @60
    @4
    @15
    @78
    @69
    @60
    @4
    wa
    #
    @15
    wa
    @78
    @31
    cV
    wcel
    #
    @69
    @80
    @81
    @15
    @78
    @80
    @27
    cV
    cword
    #
    wcel
    #
    @27
    c0
    wne
    #
    wa
    #
    @81
    @60
    @4
    @85
    @60
    @55
    @30
    wa
    #
    @4
    @85
    wi
    #
    @11
    @30
    vw
    @27
    @12
    @9
    @27
    wceq
    @10
    @29
    cP
    cc0
    @9
    @27
    fveq1
    eqeq1d
    elrab
    @86
    @83
    @27
    chash
    cfv
    #
    @16
    wceq
    #
    vi
    cv
    #
    @27
    cfv
    @90
    c1
    caddc
    co
    @27
    cfv
    cpr
    @32
    wcel
    vi
    cc0
    cN
    cfzo
    co
    wral
    #
    w3a
    #
    @87
    @55
    @92
    @30
    vi
    @32
    cG
    cN
    cV
    @27
    rusgrnumwwlk.v
    @44
    wwlknp
    adantr
    @83
    @89
    @87
    @91
    @83
    @89
    wa
    #
    @4
    @85
    @93
    @4
    wa
    #
    @83
    @84
    @83
    @89
    @4
    simpll
    @94
    @84
    cc0
    @88
    clt
    wbr
    #
    @94
    @95
    cc0
    @16
    clt
    wbr
    #
    @4
    @96
    @93
    @3
    @1
    @96
    @2
    cN
    nn0p1gt0
    3ad2ant3
    adantl
    @89
    @95
    @96
    wb
    @83
    @4
    @88
    @16
    cc0
    clt
    breq2
    ad2antlr
    mpbird
    @94
    @84
    @95
    @83
    @84
    wn
    #
    @95
    wn
    #
    wb
    @89
    @4
    @83
    @88
    cc0
    cle
    wbr
    #
    @27
    c0
    wceq
    #
    @98
    @97
    @27
    @82
    hashle00
    @83
    @88
    cr
    wcel
    #
    cc0
    cr
    wcel
    #
    @98
    @99
    wb
    @83
    @88
    cV
    @27
    lencl
    nn0red
    0re
    @101
    @102
    wa
    @99
    @98
    @88
    cc0
    lenlt
    bicomd
    sylancl
    @97
    @100
    wb
    @83
    @27
    c0
    nne
    a1i
    3bitr4rd
    ad2antrr
    con4bid
    mpbird
    jca
    ex
    3adant3
    syl
    sylbi
    imp
    cV
    @27
    lswcl
    syl
    ad2antrr
    @77
    @69
    vp
    @31
    cV
    @72
    @31
    wceq
    #
    @76
    @68
    cK
    @103
    @75
    @67
    chash
    @103
    @74
    @66
    vn
    cV
    @103
    @73
    @65
    @32
    @72
    @31
    @64
    preq1
    eleq1d
    rabbidv
    fveq2d
    eqeq1d
    rspcva
    sylancom
    exp41
    com14
    3ad2ant3
    syl
    imp41
    3eqtrd
    sumeq2dv
    @22
    @14
    cK
    cmul
    co
    #
    @7
    cK
    cmul
    co
    #
    @59
    @18
    @15
    @104
    @105
    wceq
    @5
    @14
    @7
    cK
    cmul
    oveq1
    adantl
    @22
    @13
    cfn
    wcel
    #
    cK
    cc
    wcel
    #
    @59
    @104
    wceq
    @22
    @12
    cfn
    wcel
    #
    @106
    @4
    @108
    @0
    @15
    @1
    @2
    @108
    @3
    @1
    @57
    @108
    @58
    cG
    cN
    wwlksnfi
    sylbi
    3ad2ant1
    ad2antlr
    @11
    vw
    @12
    rabfi
    syl
    @5
    @107
    @15
    @5
    cK
    @5
    cG
    cfusgr
    wcel
    #
    @0
    cV
    c0
    wne
    #
    cK
    cn0
    wcel
    @5
    @70
    @1
    wa
    @109
    @0
    @70
    @4
    @1
    cG
    cK
    rusgrusgr
    @1
    @2
    @3
    simp1
    anim12i
    cG
    cV
    rusgrnumwwlk.v
    isfusgr
    sylibr
    @0
    @4
    simpl
    @4
    @110
    @0
    @2
    @1
    @110
    @3
    cV
    cP
    ne0i
    3ad2ant2
    adantl
    cG
    cK
    cV
    rusgrnumwwlk.v
    frusgrnn0
    syl3anc
    nn0cnd
    #
    adantr
    @13
    cK
    vy
    fsumconst
    syl2anc
    @5
    @18
    @105
    wceq
    @15
    @5
    cK
    cN
    @111
    @21
    expp1d
    adantr
    3eqtr4d
    eqtrd
    3eqtrd
    @5
    @19
    @26
    wb
    #
    @15
    @5
    @2
    @16
    cn0
    wcel
    #
    @112
    @20
    @4
    @113
    @0
    @3
    @1
    @113
    @2
    cN
    peano2nn0
    3ad2ant3
    adantl
    @2
    @113
    wa
    @17
    @25
    @18
    vw
    vv
    cP
    vn
    cG
    cL
    @16
    cV
    rusgrnumwwlk.v
    rusgrnumwwlk.l
    rusgrnumwwlklem
    eqeq1d
    syl2anc
    adantr
    mpbird
    ex
    sylbid
end
