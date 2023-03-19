include "cop.mm"
include "cxp.mm"
include "wcel.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "wrex.mm"
include "wi.mm"
include "cmpt2.mm"
include "crn.mm"
include "wral.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "cflf.mm"
include "cfv.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "xpex.mm"
include "rgen2w.mm"
include "eqid.mm"
include "wceq.mm"
include "eleq2.mm"
include "sseq2.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "ralrnmpt2.mm"
include "ax-mp.mm"
include "crab.mm"
include "opelxp.mm"
include "ancom.mm"
include "bitri.mm"
include "a1i.mm"
include "r19.40.mm"
include "raleq.mm"
include "cbvrexv.mm"
include "anbi12i.mm"
include "sylib.mm"
include "reeanv.mm"
include "cin.mm"
include "cfil.mm"
include "filin.mm"
include "3expb.mm"
include "sylan.mm"
include "inss1.mm"
include "ssralv.mm"
include "inss2.mm"
include "anim12i.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2an.mm"
include "ex.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "impbid2.mm"
include "cmpt.mm"
include "cres.mm"
include "df-ima.mm"
include "filelss.mm"
include "reseq1i.mm"
include "resmpt.mm"
include "syl5eq.mm"
include "syl.mm"
include "rneqd.mm"
include "sseq1d.mm"
include "ralbii.mm"
include "wf.mm"
include "fmpt.mm"
include "wfn.mm"
include "opex.mm"
include "fnmpti.mm"
include "df-f.mm"
include "mpbiran.mm"
include "r19.26.mm"
include "3bitr3i.mm"
include "syl6bb.mm"
include "rexbidva.mm"
include "wfun.mm"
include "cdm.mm"
include "adantr.mm"
include "ffun.mm"
include "fdm.mm"
include "sseqtr4d.mm"
include "funimass4.mm"
include "syl2anc.mm"
include "3bitr4d.mm"
include "impexp.mm"
include "ralbidv.mm"
include "ralrab.mm"
include "r19.21v.mm"
include "bitr3i.mm"
include "syl6bbr.mm"
include "c0.mm"
include "wne.mm"
include "ctopon.mm"
include "toponmax.mm"
include "rabn0.mm"
include "sylibr.mm"
include "anim12dan.mm"
include "r19.28zv.mm"
include "r19.27zv.mm"
include "sylan9bbr.mm"
include "bitrd.mm"
include "syl5bb.mm"
include "pm5.32da.mm"
include "anbi1i.mm"
include "an4.mm"
include "3bitr4g.mm"
include "ctg.mm"
include "txval.mm"
include "oveq1d.mm"
include "fveq1d.mm"
include "eleq2d.mm"
include "txtopon.mm"
include "eqeltrrd.mm"
include "ffvelrnda.mm"
include "opelxpi.mm"
include "fmptd.mm"
include "flftg.mm"
include "syl3anc.mm"
include "isflf.mm"

theorem txflf
  let wph: wff ph
  let cR: class R
  let cS: class S
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cL: class L
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  assume txflf.j: |- ( ph -> J e. ( TopOn ` X ) )
  assume txflf.k: |- ( ph -> K e. ( TopOn ` Y ) )
  assume txflf.l: |- ( ph -> L e. ( Fil ` Z ) )
  assume txflf.f: |- ( ph -> F : Z --> X )
  assume txflf.g: |- ( ph -> G : Z --> Y )
  assume txflf.h: |- H = ( n e. Z |-> <. ( F ` n ) , ( G ` n ) >. )

  disjoint n ph
  disjoint F n
  disjoint G n
  disjoint Z n
  disjoint X n
  disjoint Y n
  disjoint h u
  disjoint h v
  disjoint h z
  disjoint H h
  disjoint u v
  disjoint u z
  disjoint H u
  disjoint v z
  disjoint H v
  disjoint H z
  disjoint f g
  disjoint f h
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f ph
  disjoint g h
  disjoint g n
  disjoint g u
  disjoint g v
  disjoint g ph
  disjoint h n
  disjoint h ph
  disjoint n u
  disjoint n v
  disjoint ph u
  disjoint ph v
  disjoint h x
  disjoint R h
  disjoint u x
  disjoint R u
  disjoint v x
  disjoint R v
  disjoint x z
  disjoint R x
  disjoint R z
  disjoint S h
  disjoint S u
  disjoint S v
  disjoint S x
  disjoint S z
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F u
  disjoint F v
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G u
  disjoint G v
  disjoint f x
  disjoint f z
  disjoint J f
  disjoint J h
  disjoint J u
  disjoint J v
  disjoint J x
  disjoint J z
  disjoint g x
  disjoint g z
  disjoint K g
  disjoint K h
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint K z
  disjoint L f
  disjoint L g
  disjoint L h
  disjoint L u
  disjoint L v
  disjoint L z
  disjoint Z f
  disjoint Z g
  disjoint Z h
  disjoint Z u
  disjoint Z v
  disjoint X f
  disjoint X h
  disjoint n x
  disjoint X u
  disjoint X x
  disjoint Y g
  disjoint Y h
  disjoint Y v
  disjoint Y x
  assert |- ( ph -> ( <. R , S >. e. ( ( ( J tX K ) fLimf L ) ` H ) <-> ( R e. ( ( J fLimf L ) ` F ) /\ S e. ( ( K fLimf L ) ` G ) ) ) )

  proof
    wph
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
    @0
    vz
    cv
    #
    wcel
    #
    cH
    vh
    cv
    #
    cima
    #
    @3
    wss
    #
    vh
    cL
    wrex
    #
    wi
    #
    vz
    vu
    vv
    cJ
    cK
    vu
    cv
    #
    vv
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    wral
    #
    wa
    #
    cR
    cX
    wcel
    #
    cR
    @10
    wcel
    #
    cF
    vf
    cv
    #
    cima
    @10
    wss
    #
    vf
    cL
    wrex
    #
    wi
    vu
    cJ
    wral
    #
    wa
    #
    cS
    cY
    wcel
    #
    cS
    @11
    wcel
    #
    cG
    vg
    cv
    #
    cima
    @11
    wss
    #
    vg
    cL
    wrex
    #
    wi
    vv
    cK
    wral
    #
    wa
    #
    wa
    #
    @0
    cH
    cJ
    cK
    ctx
    co
    #
    cL
    cflf
    co
    #
    cfv
    #
    wcel
    #
    cR
    cF
    cJ
    cL
    cflf
    co
    cfv
    wcel
    #
    cS
    cG
    cK
    cL
    cflf
    co
    cfv
    wcel
    #
    wa
    wph
    @17
    @24
    wa
    #
    @15
    wa
    @38
    @22
    @29
    wa
    #
    wa
    @16
    @31
    wph
    @38
    @15
    @39
    @15
    @0
    @12
    wcel
    #
    @6
    @12
    wss
    #
    vh
    cL
    wrex
    #
    wi
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
    @38
    wa
    #
    @39
    @12
    cvv
    wcel
    #
    vv
    cK
    wral
    vu
    cJ
    wral
    @15
    @45
    wb
    @47
    vu
    vv
    cJ
    cK
    @10
    @11
    vu
    vex
    vv
    vex
    xpex
    rgen2w
    @9
    @43
    vu
    vv
    vz
    cJ
    cK
    @12
    @13
    cvv
    @13
    eqid
    @3
    @12
    wceq
    #
    @4
    @40
    @8
    @42
    @3
    @12
    @0
    eleq2
    @48
    @7
    @41
    vh
    cL
    @3
    @12
    @6
    sseq2
    rexbidv
    imbi12d
    ralrnmpt2
    ax-mp
    @46
    @45
    @21
    vu
    cR
    vx
    cv
    #
    wcel
    #
    vx
    cJ
    crab
    #
    wral
    #
    @28
    vv
    cS
    @49
    wcel
    #
    vx
    cK
    crab
    #
    wral
    #
    wa
    #
    @39
    @46
    @45
    @21
    @28
    wa
    #
    vv
    @54
    wral
    #
    vu
    @51
    wral
    #
    @56
    wph
    @45
    @59
    wb
    @38
    wph
    @45
    @18
    @58
    wi
    #
    vu
    cJ
    wral
    @59
    wph
    @44
    @60
    vu
    cJ
    wph
    @44
    @25
    @18
    @57
    wi
    #
    wi
    #
    vv
    cK
    wral
    #
    @60
    wph
    @43
    @62
    vv
    cK
    wph
    @43
    @25
    @18
    wa
    #
    @57
    wi
    @62
    wph
    @40
    @64
    @42
    @57
    @40
    @64
    wb
    wph
    @40
    @18
    @25
    wa
    @64
    cR
    cS
    @10
    @11
    opelxp
    @18
    @25
    ancom
    bitri
    a1i
    wph
    vn
    cv
    #
    cF
    cfv
    #
    @10
    wcel
    #
    vn
    @5
    wral
    #
    @65
    cG
    cfv
    #
    @11
    wcel
    #
    vn
    @5
    wral
    #
    wa
    #
    vh
    cL
    wrex
    #
    @67
    vn
    @19
    wral
    #
    vf
    cL
    wrex
    #
    @70
    vn
    @26
    wral
    #
    vg
    cL
    wrex
    #
    wa
    #
    @42
    @57
    wph
    @73
    @78
    @73
    @68
    vh
    cL
    wrex
    #
    @71
    vh
    cL
    wrex
    #
    wa
    @78
    @68
    @71
    vh
    cL
    r19.40
    @79
    @75
    @80
    @77
    @68
    @74
    vh
    vf
    cL
    @67
    vn
    @5
    @19
    raleq
    cbvrexv
    @71
    @76
    vh
    vg
    cL
    @70
    vn
    @5
    @26
    raleq
    cbvrexv
    anbi12i
    sylib
    @78
    @74
    @76
    wa
    #
    vg
    cL
    wrex
    vf
    cL
    wrex
    wph
    @73
    @74
    @76
    vf
    vg
    cL
    cL
    reeanv
    wph
    @81
    @73
    vf
    vg
    cL
    cL
    wph
    @19
    cL
    wcel
    #
    @26
    cL
    wcel
    #
    wa
    #
    wa
    #
    @81
    @73
    @85
    @19
    @26
    cin
    #
    cL
    wcel
    #
    @67
    vn
    @86
    wral
    #
    @70
    vn
    @86
    wral
    #
    wa
    #
    @73
    @81
    wph
    cL
    cZ
    cfil
    cfv
    wcel
    #
    @84
    @87
    txflf.l
    @91
    @82
    @83
    @87
    @19
    @26
    cL
    cZ
    filin
    3expb
    sylan
    @74
    @88
    @76
    @89
    @86
    @19
    wss
    @74
    @88
    wi
    @19
    @26
    inss1
    @67
    vn
    @86
    @19
    ssralv
    ax-mp
    @86
    @26
    wss
    @76
    @89
    wi
    @19
    @26
    inss2
    @70
    vn
    @86
    @26
    ssralv
    ax-mp
    anim12i
    @72
    @90
    vh
    @86
    cL
    @5
    @86
    wceq
    @68
    @88
    @71
    @89
    @67
    vn
    @5
    @86
    raleq
    @70
    vn
    @5
    @86
    raleq
    anbi12d
    rspcev
    syl2an
    ex
    rexlimdvva
    syl5bir
    impbid2
    wph
    @41
    @72
    vh
    cL
    wph
    @5
    cL
    wcel
    #
    wa
    #
    @41
    vn
    @5
    @66
    @69
    cop
    #
    cmpt
    #
    crn
    #
    @12
    wss
    #
    @72
    @93
    @6
    @96
    @12
    @93
    @6
    cH
    @5
    cres
    #
    crn
    @96
    cH
    @5
    df-ima
    @93
    @98
    @95
    @93
    @5
    cZ
    wss
    #
    @98
    @95
    wceq
    wph
    @91
    @92
    @99
    txflf.l
    @5
    cL
    cZ
    filelss
    sylan
    @99
    @98
    vn
    cZ
    @94
    cmpt
    #
    @5
    cres
    @95
    cH
    @100
    @5
    txflf.h
    reseq1i
    vn
    cZ
    @5
    @94
    resmpt
    syl5eq
    syl
    rneqd
    syl5eq
    sseq1d
    @94
    @12
    wcel
    #
    vn
    @5
    wral
    #
    @67
    @70
    wa
    #
    vn
    @5
    wral
    @97
    @72
    @101
    @103
    vn
    @5
    @66
    @69
    @10
    @11
    opelxp
    ralbii
    @102
    @5
    @12
    @95
    wf
    #
    @97
    vn
    @5
    @12
    @94
    @95
    @95
    eqid
    #
    fmpt
    @104
    @95
    @5
    wfn
    @97
    vn
    @5
    @94
    @95
    @66
    @69
    opex
    @105
    fnmpti
    @5
    @12
    @95
    df-f
    mpbiran
    bitri
    @67
    @70
    vn
    @5
    r19.26
    3bitr3i
    syl6bb
    rexbidva
    wph
    @21
    @75
    @28
    @77
    wph
    @20
    @74
    vf
    cL
    wph
    @82
    wa
    #
    cF
    wfun
    #
    @19
    cF
    cdm
    #
    wss
    @20
    @74
    wb
    @106
    cZ
    cX
    cF
    wf
    #
    @107
    wph
    @109
    @82
    txflf.f
    adantr
    #
    cZ
    cX
    cF
    ffun
    syl
    @106
    @19
    cZ
    @108
    wph
    @91
    @82
    @19
    cZ
    wss
    txflf.l
    @19
    cL
    cZ
    filelss
    sylan
    @106
    @109
    @108
    cZ
    wceq
    @110
    cZ
    cX
    cF
    fdm
    syl
    sseqtr4d
    vn
    @19
    @10
    cF
    funimass4
    syl2anc
    rexbidva
    wph
    @27
    @76
    vg
    cL
    wph
    @83
    wa
    #
    cG
    wfun
    #
    @26
    cG
    cdm
    #
    wss
    @27
    @76
    wb
    @111
    cZ
    cY
    cG
    wf
    #
    @112
    wph
    @114
    @83
    txflf.g
    adantr
    #
    cZ
    cY
    cG
    ffun
    syl
    @111
    @26
    cZ
    @113
    wph
    @91
    @83
    @26
    cZ
    wss
    txflf.l
    @26
    cL
    cZ
    filelss
    sylan
    @111
    @114
    @113
    cZ
    wceq
    @115
    cZ
    cY
    cG
    fdm
    syl
    sseqtr4d
    vn
    @26
    @11
    cG
    funimass4
    syl2anc
    rexbidva
    anbi12d
    3bitr4d
    imbi12d
    @25
    @18
    @57
    impexp
    syl6bb
    ralbidv
    @63
    @61
    vv
    @54
    wral
    @60
    @53
    @25
    @61
    vv
    vx
    cK
    @49
    @11
    cS
    eleq2
    #
    ralrab
    @18
    @57
    vv
    @54
    r19.21v
    bitr3i
    syl6bb
    ralbidv
    @50
    @18
    @58
    vu
    vx
    cJ
    @49
    @10
    cR
    eleq2
    #
    ralrab
    syl6bbr
    adantr
    @46
    @51
    c0
    wne
    #
    @54
    c0
    wne
    #
    wa
    @59
    @56
    wb
    wph
    @17
    @118
    @24
    @119
    wph
    cX
    cJ
    wcel
    #
    @17
    @118
    wph
    cJ
    cX
    ctopon
    cfv
    #
    wcel
    #
    @120
    txflf.j
    cX
    cJ
    toponmax
    syl
    @120
    @17
    wa
    @50
    vx
    cJ
    wrex
    @118
    @50
    @17
    vx
    cX
    cJ
    @49
    cX
    cR
    eleq2
    rspcev
    @50
    vx
    cJ
    rabn0
    sylibr
    sylan
    wph
    cY
    cK
    wcel
    #
    @24
    @119
    wph
    cK
    cY
    ctopon
    cfv
    #
    wcel
    #
    @123
    txflf.k
    cY
    cK
    toponmax
    syl
    @123
    @24
    wa
    @53
    vx
    cK
    wrex
    @119
    @53
    @24
    vx
    cY
    cK
    @49
    cY
    cS
    eleq2
    rspcev
    @53
    vx
    cK
    rabn0
    sylibr
    sylan
    anim12dan
    @119
    @59
    @21
    @55
    wa
    #
    vu
    @51
    wral
    @118
    @56
    @119
    @58
    @126
    vu
    @51
    @21
    @28
    vv
    @54
    r19.28zv
    ralbidv
    @21
    @55
    vu
    @51
    r19.27zv
    sylan9bbr
    syl
    bitrd
    @52
    @22
    @55
    @29
    @50
    @18
    @21
    vu
    vx
    cJ
    @117
    ralrab
    @53
    @25
    @28
    vv
    vx
    cK
    @116
    ralrab
    anbi12i
    syl6bb
    syl5bb
    pm5.32da
    @2
    @38
    @15
    cR
    cS
    cX
    cY
    opelxp
    anbi1i
    @17
    @22
    @24
    @29
    an4
    3bitr4g
    wph
    @35
    @0
    cH
    @14
    ctg
    cfv
    #
    cL
    cflf
    co
    #
    cfv
    #
    wcel
    #
    @16
    wph
    @34
    @129
    @0
    wph
    cH
    @33
    @128
    wph
    @32
    @127
    cL
    cflf
    wph
    @122
    @125
    @32
    @127
    wceq
    txflf.j
    txflf.k
    vu
    vv
    @14
    cJ
    cK
    @121
    @124
    @14
    eqid
    txval
    syl2anc
    #
    oveq1d
    fveq1d
    eleq2d
    wph
    @127
    @1
    ctopon
    cfv
    #
    wcel
    @91
    cZ
    @1
    cH
    wf
    @130
    @16
    wb
    wph
    @32
    @127
    @132
    @131
    wph
    @122
    @125
    @32
    @132
    wcel
    txflf.j
    txflf.k
    cJ
    cK
    cX
    cY
    txtopon
    syl2anc
    eqeltrrd
    txflf.l
    wph
    vn
    cZ
    @94
    @1
    cH
    wph
    @65
    cZ
    wcel
    wa
    @66
    cX
    wcel
    @69
    cY
    wcel
    @94
    @1
    wcel
    wph
    cZ
    cX
    @65
    cF
    txflf.f
    ffvelrnda
    wph
    cZ
    cY
    @65
    cG
    txflf.g
    ffvelrnda
    @66
    @69
    cX
    cY
    opelxpi
    syl2anc
    txflf.h
    fmptd
    @0
    @14
    vz
    cH
    @127
    cL
    @1
    cZ
    vh
    @127
    eqid
    flftg
    syl3anc
    bitrd
    wph
    @36
    @23
    @37
    @30
    wph
    @122
    @91
    @109
    @36
    @23
    wb
    txflf.j
    txflf.l
    txflf.f
    cR
    vu
    cF
    cJ
    cL
    cX
    cZ
    vf
    isflf
    syl3anc
    wph
    @125
    @91
    @114
    @37
    @30
    wb
    txflf.k
    txflf.l
    txflf.g
    cS
    vv
    cG
    cK
    cL
    cY
    cZ
    vg
    isflf
    syl3anc
    anbi12d
    3bitr4d
end
