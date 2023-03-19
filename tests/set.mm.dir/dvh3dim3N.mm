include "cpr.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wn.mm"
include "wa.mm"
include "wrex.mm"
include "wpss.mm"
include "wceq.mm"
include "wo.mm"
include "wss.mm"
include "clss.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "adantr.mm"
include "lspprcl.mm"
include "simpr.mm"
include "lspprid2.mm"
include "lspprss.mm"
include "sspss.mm"
include "sylib.mm"
include "csn.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lspprat.mm"
include "wi.mm"
include "w3a.mm"
include "chlt.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "dvh3dim2.mm"
include "clsm.mm"
include "co.mm"
include "csubg.mm"
include "lsssssubg.mm"
include "syl.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "prssi.mm"
include "snsspr1.mm"
include "a1i.mm"
include "lspss.mm"
include "syl3anc.mm"
include "simp3.mm"
include "sseqtrd.mm"
include "lsmless2.mm"
include "lsmpr.mm"
include "prcom.mm"
include "fveq2i.mm"
include "syl5eq.mm"
include "3sstr4d.mm"
include "ssneld.mm"
include "snsspr2.mm"
include "anim12d.mm"
include "reximdv.mm"
include "mpd.mm"
include "rexlimdv3a.mm"
include "wb.mm"
include "eleq2i.mm"
include "notbii.mm"
include "eleq2.mm"
include "notbid.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "mpbid.mm"
include "jaodan.mm"
include "syldan.mm"
include "cplusg.mm"
include "simpl1l.mm"
include "simpl2.mm"
include "lmodvacl.mm"
include "simpl3l.mm"
include "sylnib.mm"
include "lssvancl2.mm"
include "simpl1r.mm"
include "lssvancl1.mm"
include "eleq1.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "pm2.61dan.mm"

theorem dvh3dim3N
  let wph: wff ph
  let vz: setvar z
  let cT: class T
  let cU: class U
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vp: setvar p
  let c.0: class .0.
  let vw: setvar w
  assume dvh3dim.h: |- H = ( LHyp ` K )
  assume dvh3dim.u: |- U = ( ( DVecH ` K ) ` W )
  assume dvh3dim.v: |- V = ( Base ` U )
  assume dvh3dim.n: |- N = ( LSpan ` U )
  assume dvh3dim.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume dvh3dim.x: |- ( ph -> X e. V )
  assume dvh3dim.y: |- ( ph -> Y e. V )
  assume dvh3dim2.z: |- ( ph -> Z e. V )
  assume dvh3dim3.t: |- ( ph -> T e. V )

  disjoint N z
  disjoint U z
  disjoint V z
  disjoint X z
  disjoint Y z
  disjoint Z z
  disjoint ph z
  disjoint T z
  disjoint K p
  disjoint p z
  disjoint N p
  disjoint .0. p
  disjoint .0. z
  disjoint U p
  disjoint V p
  disjoint W p
  disjoint X p
  disjoint Y p
  disjoint Z p
  disjoint p ph
  disjoint N w
  disjoint U w
  disjoint V w
  disjoint X w
  disjoint Y w
  disjoint Z w
  disjoint ph w
  disjoint w z
  disjoint T w
  assert |- ( ph -> E. z e. V ( -. z e. ( N ` { X , Y } ) /\ -. z e. ( N ` { Z , T } ) ) )

  proof
    wph
    cY
    cZ
    cT
    cpr
    cN
    cfv
    #
    wcel
    #
    vz
    cv
    #
    cX
    cY
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    @2
    @0
    wcel
    #
    wn
    #
    wa
    #
    vz
    cV
    wrex
    #
    wph
    @1
    cY
    cT
    cpr
    #
    cN
    cfv
    #
    @0
    wpss
    #
    @12
    @0
    wceq
    #
    wo
    #
    @10
    wph
    @1
    wa
    #
    @12
    @0
    wss
    @15
    @16
    cU
    clss
    cfv
    #
    @0
    cN
    cU
    cY
    cT
    @17
    eqid
    #
    dvh3dim.n
    wph
    cU
    clmod
    wcel
    #
    @1
    wph
    cU
    cH
    cK
    cW
    dvh3dim.h
    dvh3dim.u
    dvh3dim.k
    dvhlmod
    #
    adantr
    wph
    @0
    @17
    wcel
    #
    @1
    wph
    @17
    cN
    cV
    cU
    cZ
    cT
    dvh3dim.v
    @18
    dvh3dim.n
    @20
    dvh3dim2.z
    dvh3dim3.t
    lspprcl
    #
    adantr
    wph
    @1
    simpr
    wph
    cT
    @0
    wcel
    @1
    wph
    cN
    cV
    cU
    cZ
    cT
    dvh3dim.v
    dvh3dim.n
    @20
    dvh3dim2.z
    dvh3dim3.t
    lspprid2
    adantr
    lspprss
    @12
    @0
    sspss
    sylib
    wph
    @13
    @10
    @14
    wph
    @13
    wa
    #
    @12
    vw
    cv
    #
    csn
    cN
    cfv
    #
    wceq
    #
    vw
    cV
    wrex
    #
    @10
    @23
    vw
    @17
    @12
    cN
    cV
    cU
    cZ
    cT
    dvh3dim.v
    @18
    dvh3dim.n
    wph
    cU
    clvec
    wcel
    @13
    wph
    cU
    cH
    cK
    cW
    dvh3dim.h
    dvh3dim.u
    dvh3dim.k
    dvhlvec
    adantr
    wph
    @12
    @17
    wcel
    @13
    wph
    @17
    cN
    cV
    cU
    cY
    cT
    dvh3dim.v
    @18
    dvh3dim.n
    @20
    dvh3dim.y
    dvh3dim3.t
    lspprcl
    adantr
    wph
    cZ
    cV
    wcel
    #
    @13
    dvh3dim2.z
    adantr
    wph
    cT
    cV
    wcel
    #
    @13
    dvh3dim3.t
    adantr
    wph
    @13
    simpr
    lspprat
    wph
    @27
    @10
    wi
    @13
    wph
    @26
    @10
    vw
    cV
    wph
    @24
    cV
    wcel
    #
    @26
    w3a
    #
    @2
    @24
    cX
    cpr
    #
    cN
    cfv
    #
    wcel
    wn
    #
    @2
    @24
    cZ
    cpr
    #
    cN
    cfv
    #
    wcel
    wn
    #
    wa
    #
    vz
    cV
    wrex
    @10
    @31
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    @24
    cX
    cZ
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    dvh3dim.n
    wph
    @30
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @26
    dvh3dim.k
    3ad2ant1
    wph
    @30
    @26
    simp2
    #
    wph
    @30
    cX
    cV
    wcel
    #
    @26
    dvh3dim.x
    3ad2ant1
    #
    wph
    @30
    @28
    @26
    dvh3dim2.z
    3ad2ant1
    #
    dvh3dim2
    @31
    @38
    @9
    vz
    cV
    @31
    @34
    @6
    @37
    @8
    @31
    @4
    @33
    @2
    @31
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    #
    cN
    cfv
    #
    cU
    clsm
    cfv
    #
    co
    #
    @43
    @25
    @46
    co
    #
    @4
    @33
    @31
    @43
    cU
    csubg
    cfv
    #
    wcel
    @25
    @49
    wcel
    #
    @45
    @25
    wss
    @47
    @48
    wss
    @31
    @17
    @49
    @43
    @31
    @19
    @17
    @49
    wss
    wph
    @30
    @19
    @26
    @20
    3ad2ant1
    #
    @17
    cU
    @18
    lsssssubg
    syl
    #
    wph
    @30
    @43
    @17
    wcel
    #
    @26
    wph
    @19
    @40
    @53
    @20
    dvh3dim.x
    @17
    cN
    cV
    cU
    cX
    dvh3dim.v
    @18
    dvh3dim.n
    lspsncl
    syl2anc
    3ad2ant1
    sseldd
    @31
    @17
    @49
    @25
    @52
    @31
    @19
    @30
    @25
    @17
    wcel
    @51
    @39
    @17
    cN
    cV
    cU
    @24
    dvh3dim.v
    @18
    dvh3dim.n
    lspsncl
    syl2anc
    sseldd
    #
    @31
    @45
    @12
    @25
    wph
    @30
    @45
    @12
    wss
    #
    @26
    wph
    @19
    @11
    cV
    wss
    #
    @44
    @11
    wss
    #
    @55
    @20
    wph
    cY
    cV
    wcel
    #
    @29
    @56
    dvh3dim.y
    dvh3dim3.t
    cY
    cT
    cV
    prssi
    syl2anc
    #
    @57
    wph
    cY
    cT
    snsspr1
    a1i
    @44
    @11
    cN
    cV
    cU
    dvh3dim.v
    dvh3dim.n
    lspss
    syl3anc
    3ad2ant1
    wph
    @30
    @26
    simp3
    #
    sseqtrd
    @46
    @43
    @45
    @25
    cU
    @46
    eqid
    #
    lsmless2
    syl3anc
    wph
    @30
    @4
    @47
    wceq
    @26
    wph
    @46
    cN
    cV
    cU
    cX
    cY
    dvh3dim.v
    dvh3dim.n
    @61
    @20
    dvh3dim.x
    dvh3dim.y
    lsmpr
    3ad2ant1
    @31
    @33
    cX
    @24
    cpr
    #
    cN
    cfv
    @48
    @32
    @62
    cN
    @24
    cX
    prcom
    fveq2i
    @31
    @46
    cN
    cV
    cU
    cX
    @24
    dvh3dim.v
    dvh3dim.n
    @61
    @51
    @41
    @39
    lsmpr
    syl5eq
    3sstr4d
    ssneld
    @31
    @0
    @36
    @2
    @31
    cZ
    csn
    cN
    cfv
    #
    cT
    csn
    #
    cN
    cfv
    #
    @46
    co
    #
    @63
    @25
    @46
    co
    #
    @0
    @36
    @31
    @63
    @49
    wcel
    @50
    @65
    @25
    wss
    @66
    @67
    wss
    @31
    @17
    @49
    @63
    @52
    wph
    @30
    @63
    @17
    wcel
    #
    @26
    wph
    @19
    @28
    @68
    @20
    dvh3dim2.z
    @17
    cN
    cV
    cU
    cZ
    dvh3dim.v
    @18
    dvh3dim.n
    lspsncl
    syl2anc
    3ad2ant1
    sseldd
    @54
    @31
    @65
    @12
    @25
    wph
    @30
    @65
    @12
    wss
    #
    @26
    wph
    @19
    @56
    @64
    @11
    wss
    #
    @69
    @20
    @59
    @70
    wph
    cY
    cT
    snsspr2
    a1i
    @64
    @11
    cN
    cV
    cU
    dvh3dim.v
    dvh3dim.n
    lspss
    syl3anc
    3ad2ant1
    @60
    sseqtrd
    @46
    @63
    @65
    @25
    cU
    @61
    lsmless2
    syl3anc
    wph
    @30
    @0
    @66
    wceq
    @26
    wph
    @46
    cN
    cV
    cU
    cZ
    cT
    dvh3dim.v
    dvh3dim.n
    @61
    @20
    dvh3dim2.z
    dvh3dim3.t
    lsmpr
    3ad2ant1
    @31
    @36
    cZ
    @24
    cpr
    #
    cN
    cfv
    @67
    @35
    @71
    cN
    @24
    cZ
    prcom
    fveq2i
    @31
    @46
    cN
    cV
    cU
    cZ
    @24
    dvh3dim.v
    dvh3dim.n
    @61
    @51
    @42
    @39
    lsmpr
    syl5eq
    3sstr4d
    ssneld
    anim12d
    reximdv
    mpd
    rexlimdv3a
    adantr
    mpd
    wph
    @14
    wa
    #
    @2
    cY
    cX
    cpr
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    @2
    @12
    wcel
    #
    wn
    #
    wa
    #
    vz
    cV
    wrex
    #
    @10
    wph
    @80
    @14
    wph
    vz
    cU
    cH
    cK
    cN
    cV
    cW
    cY
    cX
    cT
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    dvh3dim.n
    dvh3dim.k
    dvh3dim.y
    dvh3dim.x
    dvh3dim3.t
    dvh3dim2
    adantr
    @72
    @79
    @9
    vz
    cV
    @72
    @14
    @79
    @9
    wb
    wph
    @14
    simpr
    @14
    @76
    @6
    @78
    @8
    @76
    @6
    wb
    @14
    @75
    @5
    @74
    @4
    @2
    @73
    @3
    cN
    cY
    cX
    prcom
    fveq2i
    #
    eleq2i
    notbii
    a1i
    @14
    @77
    @7
    @12
    @0
    @2
    eleq2
    notbid
    anbi12d
    syl
    rexbidv
    mpbid
    jaodan
    syldan
    wph
    @1
    wn
    #
    wa
    #
    @24
    @74
    wcel
    #
    wn
    #
    @24
    @12
    wcel
    wn
    #
    wa
    #
    vw
    cV
    wrex
    #
    @10
    wph
    @88
    @82
    wph
    vw
    cU
    cH
    cK
    cN
    cV
    cW
    cY
    cX
    cT
    dvh3dim.h
    dvh3dim.u
    dvh3dim.v
    dvh3dim.n
    dvh3dim.k
    dvh3dim.y
    dvh3dim.x
    dvh3dim3.t
    dvh3dim2
    adantr
    @83
    @87
    @10
    vw
    cV
    @83
    @30
    @87
    w3a
    #
    @24
    @0
    wcel
    #
    @10
    @89
    @90
    wa
    #
    @24
    cY
    cU
    cplusg
    cfv
    #
    co
    #
    cV
    wcel
    #
    @93
    @4
    wcel
    #
    wn
    #
    @93
    @0
    wcel
    #
    wn
    #
    @10
    @91
    @19
    @30
    @58
    @94
    @91
    wph
    @19
    wph
    @82
    @30
    @87
    @90
    simpl1l
    #
    @20
    syl
    #
    @83
    @30
    @87
    @90
    simpl2
    #
    @91
    wph
    @58
    @99
    dvh3dim.y
    syl
    #
    @92
    cV
    cU
    @24
    cY
    dvh3dim.v
    @92
    eqid
    #
    lmodvacl
    syl3anc
    @91
    @92
    @17
    @4
    cV
    cU
    cY
    @24
    dvh3dim.v
    @103
    @18
    @100
    @91
    wph
    @4
    @17
    wcel
    @99
    wph
    @17
    cN
    cV
    cU
    cX
    cY
    dvh3dim.v
    @18
    dvh3dim.n
    @20
    dvh3dim.x
    dvh3dim.y
    lspprcl
    syl
    @91
    wph
    cY
    @4
    wcel
    @99
    wph
    cN
    cV
    cU
    cX
    cY
    dvh3dim.v
    dvh3dim.n
    @20
    dvh3dim.x
    dvh3dim.y
    lspprid2
    syl
    @101
    @91
    @84
    @24
    @4
    wcel
    #
    @85
    @86
    @83
    @30
    @90
    simpl3l
    @74
    @4
    @24
    @81
    eleq2i
    #
    sylnib
    lssvancl2
    @91
    @92
    @17
    @0
    cV
    cU
    @24
    cY
    dvh3dim.v
    @103
    @18
    @100
    @91
    wph
    @21
    @99
    @22
    syl
    @89
    @90
    simpr
    @102
    wph
    @82
    @30
    @87
    @90
    simpl1r
    lssvancl1
    @9
    @96
    @98
    wa
    vz
    @93
    cV
    @2
    @93
    wceq
    #
    @6
    @96
    @8
    @98
    @106
    @5
    @95
    @2
    @93
    @4
    eleq1
    notbid
    @106
    @7
    @97
    @2
    @93
    @0
    eleq1
    notbid
    anbi12d
    rspcev
    syl12anc
    @89
    @90
    wn
    #
    wa
    #
    @30
    @104
    wn
    #
    @107
    @10
    @83
    @30
    @87
    @107
    simpl2
    @108
    @84
    @104
    @85
    @86
    @83
    @30
    @107
    simpl3l
    @105
    sylnib
    @89
    @107
    simpr
    @9
    @109
    @107
    wa
    vz
    @24
    cV
    @2
    @24
    wceq
    #
    @6
    @109
    @8
    @107
    @110
    @5
    @104
    @2
    @24
    @4
    eleq1
    notbid
    @110
    @7
    @90
    @2
    @24
    @0
    eleq1
    notbid
    anbi12d
    rspcev
    syl12anc
    pm2.61dan
    rexlimdv3a
    mpd
    pm2.61dan
end
