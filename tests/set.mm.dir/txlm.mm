include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cop.mm"
include "cxp.mm"
include "ctx.mm"
include "co.mm"
include "clm.mm"
include "wbr.mm"
include "r19.27v.mm"
include "r19.28v.mm"
include "ralimi.mm"
include "syl.mm"
include "wss.mm"
include "cmpt2.mm"
include "crn.mm"
include "ctg.mm"
include "simprl.mm"
include "wceq.mm"
include "ctop.mm"
include "ctopon.mm"
include "topontop.mm"
include "eqid.mm"
include "txval.mm"
include "syl2anc.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "simprr.mm"
include "tg2.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "xpex.mm"
include "rgen2w.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rexrnmpt2.mm"
include "ax-mp.mm"
include "sylib.mm"
include "ex.mm"
include "r19.29.mm"
include "opelxp.mm"
include "pm2.27.mm"
include "im2anan9.mm"
include "rexanuz2.mm"
include "uztrn2.mm"
include "opelxpi.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "opex.mm"
include "fvmpt.mm"
include "eleq1d.mm"
include "syl5ibr.mm"
include "adantl.mm"
include "simplrr.mm"
include "sseld.mm"
include "syld.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "syl5bir.mm"
include "com23.mm"
include "impd.mm"
include "rexlimdva.mm"
include "syl5.mm"
include "expcomd.mm"
include "expdimp.mm"
include "ralrimdva.mm"
include "toponmax.mm"
include "txopn.mm"
include "syl22anc.mm"
include "rexralbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "expcom.mm"
include "opelxp1.mm"
include "syl6bi.mm"
include "reximia.mm"
include "a1i.mm"
include "imim12d.mm"
include "adantrl.mm"
include "ad2antrl.mm"
include "opelxp2.mm"
include "adantrr.mm"
include "jcad.mm"
include "impbid.mm"
include "pm5.32da.mm"
include "anbi1i.mm"
include "syl6bbr.mm"
include "eqidd.mm"
include "lmbrf.mm"
include "an4.mm"
include "syl6bb.mm"
include "txtopon.mm"
include "ffvelrnda.mm"
include "fmptd.mm"
include "3bitr4d.mm"

theorem txlm
  let wph: wff ph
  let cR: class R
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let cO: class O
  let vt: setvar t
  assume txlm.z: |- Z = ( ZZ>= ` M )
  assume txlm.m: |- ( ph -> M e. ZZ )
  assume txlm.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume txlm.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume txlm.f: |- ( ph -> F : Z --> X )
  assume txlm.g: |- ( ph -> G : Z --> Y )
  assume txlm.h: |- H = ( n e. Z |-> <. ( F ` n ) , ( G ` n ) >. )

  disjoint F n
  disjoint n ph
  disjoint G n
  disjoint J n
  disjoint K n
  disjoint X n
  disjoint Y n
  disjoint Z n
  disjoint j k
  disjoint j n
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint F j
  disjoint k n
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint F k
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint F v
  disjoint w x
  disjoint F w
  disjoint F x
  disjoint H j
  disjoint H k
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint O n
  disjoint O x
  disjoint j ph
  disjoint k ph
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint G j
  disjoint G k
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G x
  disjoint M j
  disjoint M k
  disjoint j t
  disjoint R j
  disjoint k t
  disjoint R k
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint R t
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint S j
  disjoint S k
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint J j
  disjoint J k
  disjoint n t
  disjoint J t
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint K j
  disjoint K k
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K w
  disjoint X j
  disjoint X k
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint Y j
  disjoint Y k
  disjoint Y u
  disjoint Y v
  disjoint Y w
  disjoint Y x
  disjoint Z j
  disjoint Z k
  disjoint Z u
  disjoint Z v
  disjoint Z w
  assert |- ( ph -> ( ( F ( ~~>t ` J ) R /\ G ( ~~>t ` K ) S ) <-> H ( ~~>t ` ( J tX K ) ) <. R , S >. ) )

  proof
    wph
    cR
    cX
    wcel
    #
    cS
    cY
    wcel
    #
    wa
    #
    cR
    vu
    cv
    #
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    @3
    wcel
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    cS
    vv
    cv
    #
    wcel
    #
    @5
    cG
    cfv
    #
    @14
    wcel
    #
    vk
    @9
    wral
    #
    vj
    cZ
    wrex
    #
    wi
    #
    vv
    cK
    wral
    #
    wa
    #
    wa
    #
    cR
    cS
    cop
    #
    cX
    cY
    cxp
    #
    wcel
    #
    @24
    vw
    cv
    #
    wcel
    #
    @5
    cH
    cfv
    #
    @27
    wcel
    #
    vk
    @9
    wral
    #
    vj
    cZ
    wrex
    #
    wi
    #
    vw
    cJ
    cK
    ctx
    co
    #
    wral
    #
    wa
    #
    cF
    cR
    cJ
    clm
    cfv
    wbr
    #
    cG
    cS
    cK
    clm
    cfv
    wbr
    #
    wa
    #
    cH
    @24
    @34
    clm
    cfv
    wbr
    wph
    @23
    @2
    @35
    wa
    @36
    wph
    @2
    @22
    @35
    wph
    @2
    wa
    #
    @22
    @35
    wph
    @22
    @35
    wi
    @2
    @22
    @12
    @20
    wa
    #
    vv
    cK
    wral
    #
    vu
    cJ
    wral
    #
    wph
    @35
    @22
    @12
    @21
    wa
    #
    vu
    cJ
    wral
    @43
    @12
    @21
    vu
    cJ
    r19.27v
    @44
    @42
    vu
    cJ
    @12
    @20
    vv
    cK
    r19.28v
    ralimi
    syl
    wph
    @43
    @33
    vw
    @34
    wph
    @27
    @34
    wcel
    #
    wa
    @28
    @43
    @32
    wph
    @45
    @28
    @43
    @32
    wi
    #
    wph
    @45
    @28
    wa
    #
    @24
    @3
    @14
    cxp
    #
    wcel
    #
    @48
    @27
    wss
    #
    wa
    #
    vv
    cK
    wrex
    #
    vu
    cJ
    wrex
    #
    @46
    wph
    @47
    @53
    wph
    @47
    wa
    #
    @24
    vt
    cv
    #
    wcel
    #
    @55
    @27
    wss
    #
    wa
    #
    vt
    vu
    vv
    cJ
    cK
    @48
    cmpt2
    #
    crn
    #
    wrex
    #
    @53
    @54
    @27
    @60
    ctg
    cfv
    #
    wcel
    @28
    @61
    @54
    @27
    @34
    @62
    wph
    @45
    @28
    simprl
    wph
    @34
    @62
    wceq
    #
    @47
    wph
    cJ
    ctop
    wcel
    #
    cK
    ctop
    wcel
    #
    @63
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @64
    txlm.j
    cX
    cJ
    topontop
    syl
    #
    wph
    cK
    cY
    ctopon
    cfv
    wcel
    #
    @65
    txlm.k
    cY
    cK
    topontop
    syl
    #
    vu
    vv
    @60
    cJ
    cK
    ctop
    ctop
    @60
    eqid
    txval
    syl2anc
    adantr
    eleqtrd
    wph
    @45
    @28
    simprr
    vt
    @27
    @60
    @24
    tg2
    syl2anc
    @48
    cvv
    wcel
    #
    vv
    cK
    wral
    vu
    cJ
    wral
    @61
    @53
    wb
    @70
    vu
    vv
    cJ
    cK
    @3
    @14
    vu
    vex
    vv
    vex
    xpex
    rgen2w
    @58
    @51
    vu
    vv
    vt
    cJ
    cK
    @48
    @59
    cvv
    @59
    eqid
    @55
    @48
    wceq
    @56
    @49
    @57
    @50
    @55
    @48
    @24
    eleq2
    @55
    @48
    @27
    sseq1
    anbi12d
    rexrnmpt2
    ax-mp
    sylib
    ex
    wph
    @43
    @53
    @32
    @43
    @53
    wa
    @42
    @52
    wa
    #
    vu
    cJ
    wrex
    wph
    @32
    @42
    @52
    vu
    cJ
    r19.29
    wph
    @71
    @32
    vu
    cJ
    @71
    @41
    @51
    wa
    #
    vv
    cK
    wrex
    wph
    @3
    cJ
    wcel
    #
    wa
    #
    @32
    @41
    @51
    vv
    cK
    r19.29
    @74
    @72
    @32
    vv
    cK
    @74
    @14
    cK
    wcel
    #
    wa
    #
    @41
    @51
    @32
    @76
    @51
    @41
    @32
    @76
    @51
    @41
    @32
    wi
    @76
    @51
    wa
    #
    @41
    @11
    @19
    wa
    #
    @32
    @77
    @4
    @15
    wa
    #
    @41
    @78
    wi
    @77
    @49
    @79
    @76
    @49
    @50
    simprl
    cR
    cS
    @3
    @14
    opelxp
    sylib
    @4
    @12
    @11
    @15
    @20
    @19
    @4
    @11
    pm2.27
    @15
    @19
    pm2.27
    im2anan9
    syl
    @78
    @7
    @17
    wa
    #
    vk
    @9
    wral
    #
    vj
    cZ
    wrex
    @77
    @32
    @7
    @17
    vj
    vk
    cM
    cZ
    txlm.z
    rexanuz2
    @77
    @81
    @31
    vj
    cZ
    @77
    @8
    cZ
    wcel
    #
    wa
    @80
    @30
    vk
    @9
    @77
    @82
    @5
    @9
    wcel
    #
    @80
    @30
    wi
    #
    @82
    @83
    wa
    #
    @77
    @5
    cZ
    wcel
    #
    @84
    cM
    @5
    @8
    cZ
    txlm.z
    uztrn2
    #
    @77
    @86
    wa
    #
    @80
    @29
    @48
    wcel
    #
    @30
    @86
    @80
    @89
    wi
    @77
    @80
    @89
    @86
    @6
    @16
    cop
    #
    @48
    wcel
    @6
    @16
    @3
    @14
    opelxpi
    @86
    @29
    @90
    @48
    vn
    @5
    vn
    cv
    #
    cF
    cfv
    #
    @91
    cG
    cfv
    #
    cop
    #
    @90
    cZ
    cH
    @91
    @5
    wceq
    @92
    @6
    @93
    @16
    @91
    @5
    cF
    fveq2
    @91
    @5
    cG
    fveq2
    opeq12d
    txlm.h
    @6
    @16
    opex
    fvmpt
    #
    eleq1d
    syl5ibr
    adantl
    @88
    @48
    @27
    @29
    @76
    @49
    @50
    @86
    simplrr
    sseld
    syld
    sylan2
    anassrs
    ralimdva
    reximdva
    syl5bir
    syld
    ex
    com23
    impd
    rexlimdva
    syl5
    rexlimdva
    syl5
    expcomd
    syld
    expdimp
    com23
    ralrimdva
    syl5
    adantr
    @40
    @35
    @13
    @21
    wph
    @1
    @35
    @13
    wi
    @0
    wph
    @1
    wa
    @35
    @12
    vu
    cJ
    wph
    @1
    @73
    @35
    @12
    wi
    wph
    @1
    @73
    wa
    #
    wa
    #
    @35
    @24
    @3
    cY
    cxp
    #
    wcel
    #
    @29
    @98
    wcel
    #
    vk
    @9
    wral
    #
    vj
    cZ
    wrex
    #
    wi
    #
    @12
    @97
    @98
    @34
    wcel
    #
    @35
    @103
    wi
    @97
    @64
    @65
    @73
    cY
    cK
    wcel
    #
    @104
    wph
    @64
    @96
    @67
    adantr
    wph
    @65
    @96
    @69
    adantr
    wph
    @1
    @73
    simprr
    wph
    @105
    @96
    wph
    @68
    @105
    txlm.k
    cY
    cK
    toponmax
    syl
    adantr
    @3
    cY
    cJ
    cK
    ctop
    ctop
    txopn
    syl22anc
    @33
    @103
    vw
    @98
    @34
    @27
    @98
    wceq
    #
    @28
    @99
    @32
    @102
    @27
    @98
    @24
    eleq2
    @106
    @30
    @100
    vj
    vk
    cZ
    @9
    @27
    @98
    @29
    eleq2
    rexralbidv
    imbi12d
    rspcv
    syl
    @97
    @4
    @99
    @102
    @11
    @4
    @97
    @99
    @97
    @4
    @1
    @99
    wph
    @1
    @73
    simprl
    cR
    cS
    @3
    cY
    opelxpi
    sylan2
    expcom
    @102
    @11
    wi
    @97
    @101
    @10
    vj
    cZ
    @82
    @100
    @7
    vk
    @9
    @85
    @86
    @100
    @7
    wi
    @87
    @86
    @100
    @90
    @98
    wcel
    @7
    @86
    @29
    @90
    @98
    @95
    eleq1d
    @6
    @16
    @3
    cY
    opelxp1
    syl6bi
    syl
    ralimdva
    reximia
    a1i
    imim12d
    syld
    anassrs
    ralrimdva
    adantrl
    wph
    @0
    @35
    @21
    wi
    @1
    wph
    @0
    wa
    @35
    @20
    vv
    cK
    wph
    @0
    @75
    @35
    @20
    wi
    wph
    @0
    @75
    wa
    #
    wa
    #
    @35
    @24
    cX
    @14
    cxp
    #
    wcel
    #
    @29
    @109
    wcel
    #
    vk
    @9
    wral
    #
    vj
    cZ
    wrex
    #
    wi
    #
    @20
    @108
    @109
    @34
    wcel
    #
    @35
    @114
    wi
    @108
    @64
    @65
    cX
    cJ
    wcel
    #
    @75
    @115
    wph
    @64
    @107
    @67
    adantr
    wph
    @65
    @107
    @69
    adantr
    wph
    @116
    @107
    wph
    @66
    @116
    txlm.j
    cX
    cJ
    toponmax
    syl
    adantr
    wph
    @0
    @75
    simprr
    cX
    @14
    cJ
    cK
    ctop
    ctop
    txopn
    syl22anc
    @33
    @114
    vw
    @109
    @34
    @27
    @109
    wceq
    #
    @28
    @110
    @32
    @113
    @27
    @109
    @24
    eleq2
    @117
    @30
    @111
    vj
    vk
    cZ
    @9
    @27
    @109
    @29
    eleq2
    rexralbidv
    imbi12d
    rspcv
    syl
    @108
    @15
    @110
    @113
    @19
    @0
    @15
    @110
    wi
    wph
    @75
    @0
    @15
    @110
    cR
    cS
    cX
    @14
    opelxpi
    ex
    ad2antrl
    @113
    @19
    wi
    @108
    @112
    @18
    vj
    cZ
    @82
    @111
    @17
    vk
    @9
    @85
    @86
    @111
    @17
    wi
    @87
    @86
    @111
    @90
    @109
    wcel
    @17
    @86
    @29
    @90
    @109
    @95
    eleq1d
    @6
    @16
    cX
    @14
    opelxp2
    syl6bi
    syl
    ralimdva
    reximia
    a1i
    imim12d
    syld
    anassrs
    ralrimdva
    adantrr
    jcad
    impbid
    pm5.32da
    @26
    @2
    @35
    cR
    cS
    cX
    cY
    opelxp
    anbi1i
    syl6bbr
    wph
    @39
    @0
    @13
    wa
    #
    @1
    @21
    wa
    #
    wa
    @23
    wph
    @37
    @118
    @38
    @119
    wph
    vu
    @6
    cR
    vj
    vk
    cF
    cJ
    cM
    cX
    cZ
    txlm.j
    txlm.z
    txlm.m
    txlm.f
    wph
    @86
    wa
    #
    @6
    eqidd
    lmbrf
    wph
    vv
    @16
    cS
    vj
    vk
    cG
    cK
    cM
    cY
    cZ
    txlm.k
    txlm.z
    txlm.m
    txlm.g
    @120
    @16
    eqidd
    lmbrf
    anbi12d
    @0
    @13
    @1
    @21
    an4
    syl6bb
    wph
    vw
    @29
    @24
    vj
    vk
    cH
    @34
    cM
    @25
    cZ
    wph
    @66
    @68
    @34
    @25
    ctopon
    cfv
    wcel
    txlm.j
    txlm.k
    cJ
    cK
    cX
    cY
    txtopon
    syl2anc
    txlm.z
    txlm.m
    wph
    vn
    cZ
    @94
    @25
    cH
    wph
    @91
    cZ
    wcel
    wa
    @92
    cX
    wcel
    @93
    cY
    wcel
    @94
    @25
    wcel
    wph
    cZ
    cX
    @91
    cF
    txlm.f
    ffvelrnda
    wph
    cZ
    cY
    @91
    cG
    txlm.g
    ffvelrnda
    @92
    @93
    cX
    cY
    opelxpi
    syl2anc
    txlm.h
    fmptd
    @120
    @29
    eqidd
    lmbrf
    3bitr4d
end
