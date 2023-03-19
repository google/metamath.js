include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wn.mm"
include "wceq.mm"
include "clt.mm"
include "cr.mm"
include "csup.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wral.mm"
include "wrex.mm"
include "wcel.mm"
include "cicc.mm"
include "cuni.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "syl5ss.mm"
include "icccmplem1.mm"
include "simpld.mm"
include "ne0i.mm"
include "syl.mm"
include "simprd.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "suprcl.mm"
include "syl3anc.mm"
include "syl5eqel.mm"
include "rphalfcld.mm"
include "ltaddrpd.mm"
include "rpred.mm"
include "readdcld.mm"
include "ltnled.mm"
include "mpbid.mm"
include "cif.mm"
include "ifcld.mm"
include "suprub.mm"
include "syl31anc.mm"
include "syl6breqr.mm"
include "ltled.mm"
include "letrd.mm"
include "ifboth.mm"
include "min2.mm"
include "syl5eqbr.mm"
include "w3a.mm"
include "wb.mm"
include "elicc2.mm"
include "mpbir3and.mm"
include "cmin.mm"
include "ltsubrpd.mm"
include "syl6breq.mm"
include "resubcld.mm"
include "suprlub.mm"
include "wa.mm"
include "wi.mm"
include "weq.mm"
include "oveq2.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "elrab2.mm"
include "unieq.mm"
include "sseq2d.mm"
include "cbvrexv.mm"
include "csn.mm"
include "cun.mm"
include "simpr1.mm"
include "elin.mm"
include "sylib.mm"
include "elpwid.mm"
include "simpll.mm"
include "snssd.mm"
include "unssd.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "elpw.mm"
include "sylibr.mm"
include "snfi.mm"
include "unfi.mm"
include "sylancl.mm"
include "elind.mm"
include "simplr2.mm"
include "ssun1.mm"
include "syl6ss.mm"
include "biimpa.mm"
include "simp1d.mm"
include "adantrr.mm"
include "simp2d.mm"
include "simprr.mm"
include "simplr.mm"
include "sseldd.mm"
include "adantr.mm"
include "expr.mm"
include "cbl.mm"
include "cfv.mm"
include "cioo.mm"
include "simplr3.mm"
include "lttrd.mm"
include "simp3d.mm"
include "min1.mm"
include "crp.mm"
include "rphalflt.mm"
include "ltadd2dd.mm"
include "lelttrd.mm"
include "cxr.mm"
include "rexr.mm"
include "elioo2.mm"
include "syl2an.mm"
include "bl2ioo.mm"
include "eleqtrrd.mm"
include "elun2.mm"
include "wo.mm"
include "lelttric.mm"
include "mpjaod.mm"
include "ex.mm"
include "ssrdv.mm"
include "uniun.mm"
include "unisng.mm"
include "uneq2d.mm"
include "syl5eq.mm"
include "sseqtr4d.mm"
include "3exp2.mm"
include "rexlimdv.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "mpd.mm"
include "syl6bb.mm"
include "cbvrabv.mm"
include "eqtri.mm"
include "sylanbrc.mm"
include "iftrue.mm"
include "breq1d.mm"
include "syl5ibcom.mm"
include "mtod.mm"
include "iffalse.mm"
include "eqeltrrd.mm"

theorem icccmplem2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let cG: class G
  let cJ: class J
  let cV: class V
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  assume icccmp.1: |- J = ( topGen ` ran (,) )
  assume icccmp.2: |- T = ( J |`t ( A [,] B ) )
  assume icccmp.3: |- D = ( ( abs o. - ) |` ( RR X. RR ) )
  assume icccmp.4: |- S = { x e. ( A [,] B ) | E. z e. ( ~P U i^i Fin ) ( A [,] x ) C_ U. z }
  assume icccmp.5: |- ( ph -> A e. RR )
  assume icccmp.6: |- ( ph -> B e. RR )
  assume icccmp.7: |- ( ph -> A <_ B )
  assume icccmp.8: |- ( ph -> U C_ J )
  assume icccmp.9: |- ( ph -> ( A [,] B ) C_ U. U )
  assume icccmp.10: |- ( ph -> V e. U )
  assume icccmp.11: |- ( ph -> C e. RR+ )
  assume icccmp.12: |- ( ph -> ( G ( ball ` D ) C ) C_ V )
  assume icccmp.13: |- G = sup ( S , RR , < )
  assume icccmp.14: |- R = if ( ( G + ( C / 2 ) ) <_ B , ( G + ( C / 2 ) ) , B )

  disjoint x z
  disjoint B x
  disjoint B z
  disjoint A x
  disjoint A z
  disjoint D x
  disjoint T x
  disjoint T z
  disjoint J z
  disjoint U x
  disjoint U z
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint B v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x y
  disjoint y z
  disjoint B y
  disjoint C t
  disjoint C v
  disjoint C w
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph y
  disjoint R t
  disjoint R v
  disjoint R w
  disjoint R y
  disjoint A t
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint D w
  disjoint G t
  disjoint G v
  disjoint G w
  disjoint V t
  disjoint V y
  disjoint J u
  disjoint J w
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S y
  disjoint U t
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U y
  assert |- ( ph -> B e. S )

  proof
    wph
    cR
    cB
    cS
    wph
    cG
    cC
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cB
    cle
    wbr
    #
    wn
    #
    cR
    cB
    wceq
    wph
    @2
    @1
    cG
    cle
    wbr
    #
    wph
    cG
    @1
    clt
    wbr
    @4
    wn
    wph
    cG
    @0
    wph
    cG
    cS
    cr
    clt
    csup
    #
    cr
    icccmp.13
    wph
    cS
    cr
    wss
    #
    cS
    c0
    wne
    #
    vy
    cv
    #
    vn
    cv
    #
    cle
    wbr
    #
    vy
    cS
    wral
    #
    vn
    cr
    wrex
    #
    @5
    cr
    wcel
    wph
    cS
    cA
    cB
    cicc
    co
    #
    cr
    cS
    cA
    vx
    cv
    #
    cicc
    co
    #
    vz
    cv
    #
    cuni
    #
    wss
    #
    vz
    cU
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    vx
    @13
    crab
    #
    @13
    icccmp.4
    @21
    vx
    @13
    ssrab2
    eqsstri
    wph
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    @13
    cr
    wss
    #
    icccmp.5
    icccmp.6
    cA
    cB
    iccssre
    syl2anc
    #
    syl5ss
    #
    wph
    cA
    cS
    wcel
    #
    @7
    wph
    @28
    @8
    cB
    cle
    wbr
    #
    vy
    cS
    wral
    #
    wph
    vx
    vy
    vz
    cA
    cB
    cD
    cS
    cT
    cU
    cJ
    icccmp.1
    icccmp.2
    icccmp.3
    icccmp.4
    icccmp.5
    icccmp.6
    icccmp.7
    icccmp.8
    icccmp.9
    icccmplem1
    #
    simpld
    #
    cS
    cA
    ne0i
    syl
    #
    wph
    @24
    @30
    @12
    icccmp.6
    wph
    @28
    @30
    @31
    simprd
    @11
    @30
    vn
    cB
    cr
    @9
    cB
    wceq
    @10
    @29
    vy
    cS
    @9
    cB
    @8
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    vn
    vy
    cS
    suprcl
    syl3anc
    syl5eqel
    #
    wph
    cC
    icccmp.11
    rphalfcld
    #
    ltaddrpd
    #
    wph
    cG
    @1
    @35
    wph
    cG
    @0
    @35
    wph
    @0
    @36
    rpred
    #
    readdcld
    #
    ltnled
    mpbid
    wph
    cR
    cG
    cle
    wbr
    @2
    @4
    wph
    cR
    @5
    cG
    cle
    wph
    @6
    @7
    @12
    cR
    cS
    wcel
    #
    cR
    @5
    cle
    wbr
    @27
    @33
    @34
    wph
    cR
    @13
    wcel
    #
    cA
    cR
    cicc
    co
    #
    @8
    cuni
    #
    wss
    #
    vy
    @20
    wrex
    #
    @40
    wph
    @41
    cR
    cr
    wcel
    #
    cA
    cR
    cle
    wbr
    #
    cR
    cB
    cle
    wbr
    #
    wph
    cR
    @2
    @1
    cB
    cif
    #
    cr
    icccmp.14
    wph
    @2
    @1
    cB
    cr
    @39
    icccmp.6
    ifcld
    syl5eqel
    #
    wph
    cA
    @49
    cR
    cle
    wph
    cA
    @1
    cle
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    cA
    @49
    cle
    wbr
    #
    wph
    cA
    cG
    @1
    icccmp.5
    @35
    @39
    wph
    cA
    @5
    cG
    cle
    wph
    @6
    @7
    @12
    @28
    cA
    @5
    cle
    wbr
    @27
    @33
    @34
    @32
    vn
    vy
    cS
    cA
    suprub
    syl31anc
    icccmp.13
    syl6breqr
    wph
    cG
    @1
    @35
    @39
    @37
    ltled
    letrd
    icccmp.7
    @2
    @51
    @52
    @53
    @1
    cB
    @1
    @49
    cA
    cle
    breq2
    cB
    @49
    cA
    cle
    breq2
    ifboth
    syl2anc
    icccmp.14
    syl6breqr
    wph
    cR
    @49
    cB
    cle
    icccmp.14
    wph
    @1
    cr
    wcel
    #
    @24
    @49
    cB
    cle
    wbr
    @39
    icccmp.6
    @1
    cB
    min2
    syl2anc
    syl5eqbr
    wph
    @23
    @24
    @41
    @46
    @47
    @48
    w3a
    wb
    icccmp.5
    icccmp.6
    cA
    cB
    cR
    elicc2
    syl2anc
    mpbir3and
    wph
    cG
    cC
    cmin
    co
    #
    vv
    cv
    #
    clt
    wbr
    #
    vv
    cS
    wrex
    #
    @45
    wph
    @55
    @5
    clt
    wbr
    #
    @58
    wph
    @55
    cG
    @5
    clt
    wph
    cG
    cC
    @35
    icccmp.11
    ltsubrpd
    icccmp.13
    syl6breq
    wph
    @6
    @7
    @12
    @55
    cr
    wcel
    #
    @59
    @58
    wb
    @27
    @33
    @34
    wph
    cG
    cC
    @35
    wph
    cC
    icccmp.11
    rpred
    #
    resubcld
    #
    vn
    vy
    vv
    cS
    @55
    suprlub
    syl31anc
    mpbid
    wph
    @57
    @45
    vv
    cS
    @56
    cS
    wcel
    @56
    @13
    wcel
    #
    cA
    @56
    cicc
    co
    #
    @17
    wss
    #
    vz
    @20
    wrex
    #
    wa
    wph
    @57
    @45
    wi
    #
    @21
    @66
    vx
    @56
    @13
    cS
    vx
    vv
    weq
    #
    @18
    @65
    vz
    @20
    @68
    @15
    @64
    @17
    @14
    @56
    cA
    cicc
    oveq2
    sseq1d
    rexbidv
    #
    icccmp.4
    elrab2
    wph
    @63
    @66
    @67
    @66
    @64
    vw
    cv
    #
    cuni
    #
    wss
    #
    vw
    @20
    wrex
    wph
    @63
    wa
    #
    @67
    @65
    @72
    vz
    vw
    @20
    vz
    vw
    weq
    @17
    @71
    @64
    @16
    @70
    unieq
    sseq2d
    cbvrexv
    @73
    @72
    @67
    vw
    @20
    @73
    @70
    @20
    wcel
    #
    @72
    @57
    @45
    @73
    @74
    @72
    @57
    w3a
    #
    wa
    #
    @70
    cV
    csn
    #
    cun
    #
    @20
    wcel
    @42
    @78
    cuni
    #
    wss
    #
    @45
    @76
    @19
    cfn
    @78
    @76
    @78
    cU
    wss
    @78
    @19
    wcel
    @76
    @70
    @77
    cU
    @76
    @70
    cU
    @76
    @70
    @19
    wcel
    #
    @70
    cfn
    wcel
    #
    @76
    @74
    @81
    @82
    wa
    @73
    @74
    @72
    @57
    simpr1
    @70
    @19
    cfn
    elin
    sylib
    #
    simpld
    elpwid
    @76
    cV
    cU
    @76
    wph
    cV
    cU
    wcel
    #
    wph
    @63
    @75
    simpll
    #
    icccmp.10
    syl
    #
    snssd
    unssd
    @78
    cU
    @70
    @77
    vw
    vex
    cV
    snex
    unex
    elpw
    sylibr
    @76
    @82
    @77
    cfn
    wcel
    @78
    cfn
    wcel
    @76
    @81
    @82
    @83
    simprd
    cV
    snfi
    @70
    @77
    unfi
    sylancl
    elind
    @76
    @42
    @71
    cV
    cun
    #
    @79
    @76
    vt
    @42
    @87
    @76
    vt
    cv
    #
    @42
    wcel
    #
    @88
    @87
    wcel
    #
    @76
    @89
    wa
    #
    @88
    @56
    cle
    wbr
    #
    @90
    @56
    @88
    clt
    wbr
    #
    @76
    @89
    @92
    @90
    @76
    @89
    @92
    wa
    #
    wa
    #
    @64
    @87
    @88
    @95
    @64
    @71
    @87
    @74
    @72
    @57
    @73
    @94
    simplr2
    @71
    cV
    ssun1
    syl6ss
    @95
    @88
    @64
    wcel
    #
    @88
    cr
    wcel
    #
    cA
    @88
    cle
    wbr
    #
    @92
    @76
    @89
    @97
    @92
    @91
    @97
    @98
    @88
    cR
    cle
    wbr
    #
    @76
    @89
    @97
    @98
    @99
    w3a
    #
    @76
    @23
    @46
    @89
    @100
    wb
    @76
    wph
    @23
    @85
    icccmp.5
    syl
    #
    @76
    wph
    @46
    @85
    @50
    syl
    cA
    cR
    @88
    elicc2
    syl2anc
    biimpa
    #
    simp1d
    #
    adantrr
    @76
    @89
    @98
    @92
    @91
    @97
    @98
    @99
    @102
    simp2d
    adantrr
    @76
    @89
    @92
    simprr
    @76
    @96
    @97
    @98
    @92
    w3a
    wb
    #
    @94
    @76
    @23
    @56
    cr
    wcel
    #
    @104
    @101
    @76
    @13
    cr
    @56
    @76
    wph
    @25
    @85
    @26
    syl
    wph
    @63
    @75
    simplr
    sseldd
    #
    cA
    @56
    @88
    elicc2
    syl2anc
    adantr
    mpbir3and
    sseldd
    expr
    @76
    @89
    @93
    @90
    @76
    @89
    @93
    wa
    #
    wa
    #
    @88
    cV
    wcel
    @90
    @108
    cG
    cC
    cD
    cbl
    cfv
    co
    #
    cV
    @88
    @108
    wph
    @109
    cV
    wss
    @76
    wph
    @107
    @85
    adantr
    #
    icccmp.12
    syl
    @108
    @88
    @55
    cG
    cC
    caddc
    co
    #
    cioo
    co
    #
    @109
    @108
    @88
    @112
    wcel
    #
    @97
    @55
    @88
    clt
    wbr
    #
    @88
    @111
    clt
    wbr
    #
    @76
    @89
    @97
    @93
    @103
    adantrr
    #
    @108
    @55
    @56
    @88
    @108
    wph
    @60
    @110
    @62
    syl
    #
    @76
    @105
    @107
    @106
    adantr
    @116
    @74
    @72
    @57
    @73
    @107
    simplr3
    @76
    @89
    @93
    simprr
    lttrd
    @108
    @88
    cR
    @111
    @116
    @108
    wph
    @46
    @110
    @50
    syl
    @108
    wph
    @111
    cr
    wcel
    #
    @110
    wph
    cG
    cC
    @35
    @61
    readdcld
    #
    syl
    #
    @76
    @89
    @99
    @93
    @91
    @97
    @98
    @99
    @102
    simp3d
    adantrr
    @108
    wph
    cR
    @111
    clt
    wbr
    @110
    wph
    cR
    @1
    @111
    @50
    @39
    @119
    wph
    cR
    @49
    @1
    cle
    icccmp.14
    wph
    @54
    @24
    @49
    @1
    cle
    wbr
    @39
    icccmp.6
    @1
    cB
    min1
    syl2anc
    syl5eqbr
    wph
    @0
    cC
    cG
    @38
    @61
    @35
    wph
    cC
    crp
    wcel
    #
    @0
    cC
    clt
    wbr
    icccmp.11
    cC
    rphalflt
    syl
    ltadd2dd
    lelttrd
    syl
    lelttrd
    @108
    @60
    @118
    @113
    @97
    @114
    @115
    w3a
    wb
    #
    @117
    @120
    @60
    @55
    cxr
    wcel
    @111
    cxr
    wcel
    @122
    @118
    @55
    rexr
    @111
    rexr
    @55
    @111
    @88
    elioo2
    syl2an
    syl2anc
    mpbir3and
    @108
    cG
    cr
    wcel
    #
    cC
    cr
    wcel
    @109
    @112
    wceq
    @108
    wph
    @123
    @110
    @35
    syl
    @108
    cC
    @108
    wph
    @121
    @110
    icccmp.11
    syl
    rpred
    cG
    cC
    cD
    icccmp.3
    bl2ioo
    syl2anc
    eleqtrrd
    sseldd
    @88
    cV
    @71
    elun2
    syl
    expr
    @91
    @97
    @105
    @92
    @93
    wo
    @103
    @76
    @105
    @89
    @106
    adantr
    @88
    @56
    lelttric
    syl2anc
    mpjaod
    ex
    ssrdv
    @76
    @79
    @71
    @77
    cuni
    #
    cun
    @87
    @70
    @77
    uniun
    @76
    @124
    cV
    @71
    @76
    @84
    @124
    cV
    wceq
    @86
    cV
    cU
    unisng
    syl
    uneq2d
    syl5eq
    sseqtr4d
    @44
    @80
    vy
    @78
    @20
    @8
    @78
    wceq
    @43
    @79
    @42
    @8
    @78
    unieq
    sseq2d
    rspcev
    syl2anc
    3exp2
    rexlimdv
    syl5bi
    expimpd
    syl5bi
    rexlimdv
    mpd
    @64
    @43
    wss
    #
    vy
    @20
    wrex
    #
    @45
    vv
    cR
    @13
    cS
    @56
    cR
    wceq
    #
    @125
    @44
    vy
    @20
    @127
    @64
    @42
    @43
    @56
    cR
    cA
    cicc
    oveq2
    sseq1d
    rexbidv
    cS
    @22
    @126
    vv
    @13
    crab
    icccmp.4
    @21
    @126
    vx
    vv
    @13
    @68
    @21
    @66
    @126
    @69
    @65
    @125
    vz
    vy
    @20
    vz
    vy
    weq
    @17
    @43
    @64
    @16
    @8
    unieq
    sseq2d
    cbvrexv
    syl6bb
    cbvrabv
    eqtri
    elrab2
    sylanbrc
    #
    vn
    vy
    cS
    cR
    suprub
    syl31anc
    icccmp.13
    syl6breqr
    @2
    cR
    @1
    cG
    cle
    @2
    cR
    @49
    @1
    icccmp.14
    @2
    @1
    cB
    iftrue
    syl5eq
    breq1d
    syl5ibcom
    mtod
    @3
    cR
    @49
    cB
    icccmp.14
    @2
    @1
    cB
    iffalse
    syl5eq
    syl
    @128
    eqeltrrd
end
