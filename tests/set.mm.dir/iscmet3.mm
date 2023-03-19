include "cms.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wf.mm"
include "clm.mm"
include "cdm.mm"
include "wi.mm"
include "cca.mm"
include "wral.mm"
include "wa.mm"
include "cmetcau.mm"
include "a1d.mm"
include "ralrimiva.mm"
include "cme.mm"
include "cflim.mm"
include "co.mm"
include "c0.mm"
include "wne.mm"
include "ccfil.mm"
include "adantr.mm"
include "cz.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "cexp.mm"
include "clt.mm"
include "wbr.mm"
include "wex.mm"
include "wrex.mm"
include "crp.mm"
include "simpr.mm"
include "1rp.mm"
include "rphalfcl.mm"
include "ax-mp.mm"
include "rpexpcl.mm"
include "mpan.mm"
include "cfili.mm"
include "syl2an.mm"
include "vex.mm"
include "cn.mm"
include "com.mm"
include "znnen.mm"
include "nnenom.mm"
include "entri.mm"
include "raleq.mm"
include "raleqbi1dv.mm"
include "axcc4.mm"
include "syl.mm"
include "cid.mm"
include "cfz.mm"
include "cdom.mm"
include "ciin.mm"
include "cen.mm"
include "ad2antrr.mm"
include "uzenom.mm"
include "endom.mm"
include "3syl.mm"
include "crab.mm"
include "cin.mm"
include "dfin5.mm"
include "wss.mm"
include "wceq.mm"
include "cuz.mm"
include "fzn0.mm"
include "biimpri.mm"
include "eleq2s.mm"
include "simprr.mm"
include "elfzelz.mm"
include "ffvelrn.mm"
include "cfil.mm"
include "cxmt.mm"
include "metxmet.mm"
include "simpl.mm"
include "cfilfil.mm"
include "filelss.mm"
include "sylan.mm"
include "syldan.mm"
include "r19.2z.mm"
include "syl2anr.mm"
include "iinss.mm"
include "elfvdm.mm"
include "fvi.mm"
include "sseqtr4d.mm"
include "sseqin2.mm"
include "sylib.mm"
include "syl5eqr.mm"
include "cfi.mm"
include "cfn.mm"
include "adantl.mm"
include "fzfid.mm"
include "iinfi.mm"
include "syl13anc.mm"
include "filfi.mm"
include "eleqtrd.mm"
include "fileln0.mm"
include "syl2anc.mm"
include "eqnetrd.mm"
include "rabn0.mm"
include "adantrrr.mm"
include "fvex.mm"
include "eleq1.mm"
include "cvv.mm"
include "wb.mm"
include "eliin.mm"
include "syl6bb.mm"
include "axcc4dom.mm"
include "wal.mm"
include "df-ral.mm"
include "19.29.mm"
include "sylanb.mm"
include "simprrl.mm"
include "feq3.mm"
include "4syl.mm"
include "mpbid.mm"
include "simplrr.mm"
include "simprd.mm"
include "weq.mm"
include "fveq2.mm"
include "oveq2.mm"
include "breq2d.mm"
include "raleqbidv.mm"
include "cbvralv.mm"
include "simprrr.mm"
include "eleq2d.mm"
include "eleq1d.mm"
include "syl5bb.mm"
include "simplrl.mm"
include "simpld.mm"
include "iscmet3lem1.mm"
include "simprl.mm"
include "mp2d.mm"
include "iscmet3lem2.mm"
include "ex.mm"
include "exlimdv.mm"
include "syl5.mm"
include "expdimp.mm"
include "an32s.mm"
include "mpd.mm"
include "expr.mm"
include "iscmet.mm"
include "sylanbrc.mm"
include "impbid2.mm"

theorem iscmet3
  let wph: wff ph
  let cD: class D
  let vf: setvar f
  let cJ: class J
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vg: setvar g
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vs: setvar s
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let cR: class R
  let cF: class F
  let cS: class S
  assume iscmet3.1: |- Z = ( ZZ>= ` M )
  assume iscmet3.2: |- J = ( MetOpen ` D )
  assume iscmet3.3: |- ( ph -> M e. ZZ )
  assume iscmet3.4: |- ( ph -> D e. ( Met ` X ) )

  disjoint D f
  disjoint X f
  disjoint J f
  disjoint Z f
  disjoint M f
  disjoint f ph
  disjoint f g
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f n
  disjoint f r
  disjoint f s
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f x
  disjoint f y
  disjoint g i
  disjoint g j
  disjoint g k
  disjoint g n
  disjoint g r
  disjoint g s
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g y
  disjoint D g
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i r
  disjoint i s
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint i y
  disjoint D i
  disjoint j k
  disjoint j n
  disjoint j r
  disjoint j s
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j x
  disjoint j y
  disjoint D j
  disjoint k n
  disjoint k r
  disjoint k s
  disjoint k t
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint D k
  disjoint n r
  disjoint n s
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint D n
  disjoint r s
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint r x
  disjoint r y
  disjoint D r
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s x
  disjoint s y
  disjoint D s
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint D t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint D u
  disjoint v x
  disjoint v y
  disjoint D v
  disjoint x y
  disjoint D x
  disjoint D y
  disjoint G j
  disjoint G k
  disjoint G r
  disjoint G x
  disjoint G y
  disjoint R j
  disjoint R k
  disjoint F j
  disjoint F k
  disjoint F n
  disjoint F r
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint X g
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint X n
  disjoint X r
  disjoint X s
  disjoint X x
  disjoint X y
  disjoint J g
  disjoint J i
  disjoint J j
  disjoint J k
  disjoint J n
  disjoint J r
  disjoint J s
  disjoint J x
  disjoint J y
  disjoint S k
  disjoint S n
  disjoint S u
  disjoint S v
  disjoint S y
  disjoint Z g
  disjoint Z i
  disjoint Z j
  disjoint Z k
  disjoint Z n
  disjoint Z r
  disjoint Z s
  disjoint Z y
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M n
  disjoint M x
  disjoint g ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  disjoint n ph
  disjoint ph r
  disjoint ph s
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( D e. ( CMet ` X ) <-> A. f e. ( Cau ` D ) ( f : Z --> X -> f e. dom ( ~~>t ` J ) ) ) )

  proof
    wph
    cD
    cX
    cms
    cfv
    wcel
    #
    cZ
    cX
    vf
    cv
    #
    wf
    #
    @1
    cJ
    clm
    cfv
    cdm
    wcel
    #
    wi
    #
    vf
    cD
    cca
    cfv
    #
    wral
    #
    @0
    @4
    vf
    @5
    @0
    @1
    @5
    wcel
    #
    wa
    @3
    @2
    cD
    @1
    cJ
    cX
    iscmet3.2
    cmetcau
    a1d
    ralrimiva
    wph
    @6
    @0
    wph
    @6
    wa
    #
    cD
    cX
    cme
    cfv
    wcel
    #
    cJ
    vg
    cv
    #
    cflim
    co
    c0
    wne
    #
    vg
    cD
    ccfil
    cfv
    #
    wral
    @0
    wph
    @9
    @6
    iscmet3.4
    adantr
    #
    @8
    @11
    vg
    @12
    @8
    @10
    @12
    wcel
    #
    wa
    #
    cz
    @10
    vs
    cv
    #
    wf
    #
    vu
    cv
    vv
    cv
    cD
    co
    #
    c1
    c2
    cdiv
    co
    #
    vk
    cv
    #
    cexp
    co
    #
    clt
    wbr
    #
    vv
    @20
    @16
    cfv
    #
    wral
    #
    vu
    @23
    wral
    #
    vk
    cz
    wral
    #
    wa
    #
    vs
    wex
    #
    @11
    @15
    @22
    vv
    vt
    cv
    #
    wral
    #
    vu
    @29
    wral
    #
    vt
    @10
    wrex
    #
    vk
    cz
    wral
    @28
    @15
    @32
    vk
    cz
    @15
    @14
    @21
    crp
    wcel
    #
    @32
    @20
    cz
    wcel
    #
    @8
    @14
    simpr
    @19
    crp
    wcel
    #
    @34
    @33
    c1
    crp
    wcel
    @35
    1rp
    c1
    rphalfcl
    ax-mp
    @19
    @20
    rpexpcl
    mpan
    vt
    vu
    vv
    cD
    @21
    @10
    cfili
    syl2an
    ralrimiva
    @31
    @25
    vt
    @10
    vs
    vk
    cz
    vg
    vex
    cz
    cn
    com
    znnen
    nnenom
    entri
    @30
    @24
    vu
    @29
    @23
    @22
    vv
    @29
    @23
    raleq
    raleqbi1dv
    axcc4
    syl
    @15
    @27
    @11
    vs
    @8
    @14
    @27
    @11
    @8
    @14
    @27
    wa
    #
    wa
    #
    cZ
    cX
    cid
    cfv
    #
    @1
    wf
    #
    @20
    @1
    cfv
    #
    vn
    cv
    #
    @16
    cfv
    #
    wcel
    #
    vn
    cM
    @20
    cfz
    co
    #
    wral
    #
    vk
    cZ
    wral
    #
    wa
    #
    vf
    wex
    #
    @11
    @37
    cZ
    com
    cdom
    wbr
    #
    vx
    cv
    #
    vn
    @44
    @42
    ciin
    #
    wcel
    #
    vx
    @38
    wrex
    #
    vk
    cZ
    wral
    #
    @48
    @37
    cM
    cz
    wcel
    #
    cZ
    com
    cen
    wbr
    @49
    wph
    @55
    @6
    @36
    iscmet3.3
    ad2antrr
    cM
    cZ
    iscmet3.1
    uzenom
    cZ
    com
    endom
    3syl
    @8
    @14
    @17
    @54
    @26
    @8
    @14
    @17
    wa
    #
    wa
    #
    @53
    vk
    cZ
    @57
    @20
    cZ
    wcel
    #
    wa
    #
    @52
    vx
    @38
    crab
    #
    c0
    wne
    @53
    @59
    @60
    @51
    c0
    @59
    @60
    @38
    @51
    cin
    #
    @51
    vx
    @38
    @51
    dfin5
    @59
    @51
    @38
    wss
    @61
    @51
    wceq
    @59
    @51
    cX
    @38
    @59
    @42
    cX
    wss
    #
    vn
    @44
    wrex
    #
    @51
    cX
    wss
    @58
    @44
    c0
    wne
    #
    @62
    vn
    @44
    wral
    @63
    @57
    @64
    @20
    cM
    cuz
    cfv
    #
    cZ
    @64
    @20
    @65
    wcel
    cM
    @20
    fzn0
    biimpri
    iscmet3.1
    eleq2s
    #
    @57
    @62
    vn
    @44
    @57
    @41
    @44
    wcel
    #
    @42
    @10
    wcel
    #
    @62
    @57
    @17
    @41
    cz
    wcel
    @68
    @67
    @8
    @14
    @17
    simprr
    @41
    cM
    @20
    elfzelz
    cz
    @10
    @41
    @16
    ffvelrn
    syl2an
    #
    @57
    @10
    cX
    cfil
    cfv
    #
    wcel
    #
    @68
    @62
    @8
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @14
    @71
    @56
    wph
    @72
    @6
    wph
    @9
    @72
    iscmet3.4
    cD
    cX
    metxmet
    #
    syl
    adantr
    @14
    @17
    simpl
    cD
    @10
    cX
    cfilfil
    #
    syl2an
    #
    @42
    @10
    cX
    filelss
    sylan
    syldan
    ralrimiva
    @62
    vn
    @44
    r19.2z
    syl2anr
    vn
    @44
    @42
    cX
    iinss
    syl
    @59
    @9
    cX
    cme
    cdm
    #
    wcel
    #
    @38
    cX
    wceq
    #
    @8
    @9
    @56
    @58
    @13
    ad2antrr
    cD
    cX
    cme
    elfvdm
    #
    cX
    @76
    fvi
    #
    3syl
    sseqtr4d
    @51
    @38
    sseqin2
    sylib
    syl5eqr
    @59
    @71
    @51
    @10
    wcel
    @51
    c0
    wne
    @57
    @71
    @58
    @75
    adantr
    #
    @59
    @51
    @10
    cfi
    cfv
    #
    @10
    @59
    @71
    @68
    vn
    @44
    wral
    #
    @64
    @44
    cfn
    wcel
    @51
    @82
    wcel
    @81
    @57
    @83
    @58
    @57
    @68
    vn
    @44
    @69
    ralrimiva
    adantr
    @58
    @64
    @57
    @66
    adantl
    @59
    cM
    @20
    fzfid
    vn
    @44
    @42
    @10
    @70
    iinfi
    syl13anc
    @59
    @71
    @82
    @10
    wceq
    @81
    @10
    cX
    filfi
    syl
    eleqtrd
    @51
    @10
    cX
    fileln0
    syl2anc
    eqnetrd
    @52
    vx
    @38
    rabn0
    sylib
    ralrimiva
    adantrrr
    @52
    @45
    vx
    @38
    vf
    vk
    cZ
    cX
    cid
    fvex
    @50
    @40
    wceq
    @52
    @40
    @51
    wcel
    #
    @45
    @50
    @40
    @51
    eleq1
    @40
    cvv
    wcel
    @84
    @45
    wb
    @20
    @1
    fvex
    vn
    @40
    @44
    @42
    cvv
    eliin
    ax-mp
    syl6bb
    axcc4dom
    syl2anc
    wph
    @36
    @6
    @48
    @11
    wi
    wph
    @36
    wa
    #
    @6
    @48
    @11
    @6
    @48
    wa
    @7
    @4
    wi
    #
    @47
    wa
    #
    vf
    wex
    #
    @85
    @11
    @6
    @86
    vf
    wal
    @48
    @88
    @4
    vf
    @5
    df-ral
    @86
    @47
    vf
    19.29
    sylanb
    @85
    @87
    @11
    vf
    @85
    @87
    @11
    @85
    @87
    wa
    #
    vv
    vu
    cD
    @16
    vi
    vj
    @1
    @10
    cJ
    cM
    cX
    cZ
    iscmet3.1
    iscmet3.2
    wph
    @55
    @36
    @87
    iscmet3.3
    ad2antrr
    #
    wph
    @9
    @36
    @87
    iscmet3.4
    ad2antrr
    #
    @89
    @39
    @2
    @85
    @86
    @39
    @46
    simprrl
    @89
    @9
    @77
    @78
    @39
    @2
    wb
    @91
    @79
    @80
    @38
    cX
    cZ
    @1
    feq3
    4syl
    mpbid
    #
    @89
    @26
    @18
    @19
    vi
    cv
    #
    cexp
    co
    #
    clt
    wbr
    #
    vv
    @93
    @16
    cfv
    #
    wral
    #
    vu
    @96
    wral
    #
    vi
    cz
    wral
    @89
    @17
    @26
    wph
    @14
    @27
    @87
    simplrr
    #
    simprd
    @25
    @98
    vk
    vi
    cz
    vk
    vi
    weq
    #
    @24
    @97
    vu
    @23
    @96
    @20
    @93
    @16
    fveq2
    #
    @100
    @22
    @95
    vv
    @23
    @96
    @101
    @100
    @21
    @94
    @18
    clt
    @20
    @93
    @19
    cexp
    oveq2
    breq2d
    raleqbidv
    raleqbidv
    cbvralv
    sylib
    #
    @89
    @46
    @93
    @1
    cfv
    #
    vj
    cv
    #
    @16
    cfv
    #
    wcel
    #
    vj
    cM
    @93
    cfz
    co
    #
    wral
    #
    vi
    cZ
    wral
    @85
    @86
    @39
    @46
    simprrr
    @45
    @108
    vk
    vi
    cZ
    @45
    @40
    @105
    wcel
    #
    vj
    @44
    wral
    @100
    @108
    @43
    @109
    vn
    vj
    @44
    vn
    vj
    weq
    @42
    @105
    @40
    @41
    @104
    @16
    fveq2
    eleq2d
    cbvralv
    @100
    @109
    @106
    vj
    @44
    @107
    @20
    @93
    cM
    cfz
    oveq2
    @100
    @40
    @103
    @105
    @20
    @93
    @1
    fveq2
    eleq1d
    raleqbidv
    syl5bb
    cbvralv
    sylib
    #
    @89
    @72
    @14
    @71
    @89
    @9
    @72
    @91
    @73
    syl
    wph
    @14
    @27
    @87
    simplrl
    @74
    syl2anc
    @89
    @17
    @26
    @99
    simpld
    @89
    @7
    @2
    @3
    @89
    vv
    vu
    cD
    @16
    vi
    vj
    @1
    cJ
    cM
    cX
    cZ
    iscmet3.1
    iscmet3.2
    @90
    @91
    @92
    @102
    @110
    iscmet3lem1
    @92
    @85
    @86
    @47
    simprl
    mp2d
    iscmet3lem2
    ex
    exlimdv
    syl5
    expdimp
    an32s
    mpd
    expr
    exlimdv
    mpd
    ralrimiva
    cD
    vg
    cJ
    cX
    iscmet3.2
    iscmet
    sylanbrc
    ex
    impbid2
end
