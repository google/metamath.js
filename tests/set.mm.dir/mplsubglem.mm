include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "wa.mm"
include "csupp.mm"
include "crab.mm"
include "ssrab2.mm"
include "syl6eqss.mm"
include "csn.mm"
include "cxp.mm"
include "psr0cl.mm"
include "wceq.mm"
include "cbs.mm"
include "cgrp.mm"
include "wf.mm"
include "eqid.mm"
include "grpidcl.mm"
include "fconst6g.mm"
include "3syl.mm"
include "cdif.mm"
include "eldifi.mm"
include "c0g.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "fvconst2.mm"
include "syl.mm"
include "adantl.mm"
include "suppss.mm"
include "ss0.mm"
include "eqeltrd.mm"
include "eleq2d.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "mpbir2and.mm"
include "ne0i.mm"
include "ad2antrr.mm"
include "weq.mm"
include "biimpa.mm"
include "simpld.mm"
include "adantr.mm"
include "psraddcl.mm"
include "cun.mm"
include "wi.mm"
include "wal.mm"
include "ovexd.mm"
include "simprd.mm"
include "ralrimivva.mm"
include "uneq1.mm"
include "uneq2.mm"
include "rspc2va.mm"
include "syl21anc.mm"
include "expr.mm"
include "alrimiv.mm"
include "ralrimiva.mm"
include "sseq2.mm"
include "imbi1d.mm"
include "albidv.mm"
include "rspcv.mm"
include "sylc.mm"
include "psrelbas.mm"
include "cof.mm"
include "psradd.mm"
include "fveq1d.mm"
include "ffnd.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "ovex.mm"
include "rabex2.mm"
include "a1i.mm"
include "inidm.mm"
include "eqidd.mm"
include "ofval.mm"
include "sylan2.mm"
include "ssun1.mm"
include "sscon.mm"
include "ax-mp.mm"
include "sseli.mm"
include "ssid.mm"
include "suppssr.mm"
include "adantlr.mm"
include "ssun2.mm"
include "oveq12d.mm"
include "grplid.mm"
include "mpdan.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "sseq1.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "spcgv.mm"
include "syl3c.mm"
include "psrgrp.mm"
include "grpinvcl.mm"
include "syl2an2r.mm"
include "ccom.mm"
include "psrneg.mm"
include "fvco3.mm"
include "syl2an.mm"
include "fveq2d.mm"
include "grpinvid.mm"
include "jca.mm"
include "w3a.mm"
include "wb.mm"
include "issubg2.mm"
include "mpbir3and.mm"

theorem mplsubglem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let cI: class I
  let cW: class W
  let c.0: class .0.
  let vk: setvar k
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume mplsubglem.s: |- S = ( I mPwSer R )
  assume mplsubglem.b: |- B = ( Base ` S )
  assume mplsubglem.z: |- .0. = ( 0g ` R )
  assume mplsubglem.d: |- D = { f e. ( NN0 ^m I ) | ( `' f " NN ) e. Fin }
  assume mplsubglem.i: |- ( ph -> I e. W )
  assume mplsubglem.0: |- ( ph -> (/) e. A )
  assume mplsubglem.a: |- ( ( ph /\ ( x e. A /\ y e. A ) ) -> ( x u. y ) e. A )
  assume mplsubglem.y: |- ( ( ph /\ ( x e. A /\ y C_ x ) ) -> y e. A )
  assume mplsubglem.u: |- ( ph -> U = { g e. B | ( g supp .0. ) e. A } )
  assume mplsubglem.r: |- ( ph -> R e. Grp )

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint .0. f
  disjoint g x
  disjoint g y
  disjoint .0. g
  disjoint x y
  disjoint .0. x
  disjoint .0. y
  disjoint A f
  disjoint A g
  disjoint A x
  disjoint A y
  disjoint B f
  disjoint B g
  disjoint D g
  disjoint I f
  disjoint ph x
  disjoint ph y
  disjoint S f
  disjoint S g
  disjoint S y
  disjoint f k
  disjoint f u
  disjoint g k
  disjoint g u
  disjoint k u
  disjoint k x
  disjoint k y
  disjoint .0. k
  disjoint u x
  disjoint u y
  disjoint .0. u
  disjoint D u
  disjoint k v
  disjoint k w
  disjoint k ph
  disjoint u v
  disjoint u w
  disjoint ph u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint ph w
  disjoint R k
  disjoint R v
  disjoint R w
  disjoint f v
  disjoint f w
  disjoint g v
  disjoint g w
  disjoint S k
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint U k
  disjoint U u
  disjoint U v
  disjoint U w
  assert |- ( ph -> U e. ( SubGrp ` S ) )

  proof
    wph
    cU
    cS
    csubg
    cfv
    wcel
    #
    cU
    cB
    wss
    #
    cU
    c0
    wne
    #
    vu
    cv
    #
    vv
    cv
    #
    cS
    cplusg
    cfv
    #
    co
    #
    cU
    wcel
    #
    vv
    cU
    wral
    #
    @3
    cS
    cminusg
    cfv
    #
    cfv
    #
    cU
    wcel
    #
    wa
    #
    vu
    cU
    wral
    #
    wph
    cU
    vg
    cv
    #
    c.0
    csupp
    co
    #
    cA
    wcel
    #
    vg
    cB
    crab
    #
    cB
    mplsubglem.u
    @16
    vg
    cB
    ssrab2
    syl6eqss
    wph
    cD
    c.0
    csn
    cxp
    #
    cU
    wcel
    #
    @2
    wph
    @19
    @18
    cB
    wcel
    #
    @18
    c.0
    csupp
    co
    #
    cA
    wcel
    #
    wph
    cB
    cD
    cR
    cS
    vf
    cI
    cW
    c.0
    mplsubglem.s
    mplsubglem.i
    mplsubglem.r
    mplsubglem.d
    mplsubglem.z
    mplsubglem.b
    psr0cl
    wph
    @21
    c0
    cA
    wph
    @21
    c0
    wss
    @21
    c0
    wceq
    wph
    cD
    cR
    cbs
    cfv
    #
    vu
    @18
    c0
    c.0
    wph
    cR
    cgrp
    wcel
    #
    c.0
    @23
    wcel
    #
    cD
    @23
    @18
    wf
    mplsubglem.r
    @23
    cR
    c.0
    @23
    eqid
    #
    mplsubglem.z
    grpidcl
    #
    cD
    c.0
    @23
    fconst6g
    3syl
    @3
    cD
    c0
    cdif
    wcel
    #
    @3
    @18
    cfv
    c.0
    wceq
    #
    wph
    @28
    @3
    cD
    wcel
    @29
    @3
    cD
    c0
    eldifi
    cD
    c.0
    @3
    c.0
    cR
    c0g
    cfv
    cvv
    mplsubglem.z
    cR
    c0g
    fvex
    eqeltri
    #
    fvconst2
    syl
    adantl
    suppss
    @21
    ss0
    syl
    mplsubglem.0
    eqeltrd
    wph
    @19
    @18
    @17
    wcel
    @20
    @22
    wa
    wph
    cU
    @17
    @18
    mplsubglem.u
    eleq2d
    @16
    @22
    vg
    @18
    cB
    @14
    @18
    wceq
    @15
    @21
    cA
    @14
    @18
    c.0
    csupp
    oveq1
    eleq1d
    elrab
    syl6bb
    mpbir2and
    cU
    @18
    ne0i
    syl
    wph
    @12
    vu
    cU
    wph
    @3
    cU
    wcel
    #
    wa
    #
    @8
    @11
    @32
    @7
    vv
    cU
    @32
    @4
    cU
    wcel
    #
    wa
    #
    @7
    @6
    cB
    wcel
    #
    @6
    c.0
    csupp
    co
    #
    cA
    wcel
    #
    @34
    cB
    @5
    cR
    cS
    cI
    @3
    @4
    mplsubglem.s
    mplsubglem.b
    @5
    eqid
    #
    wph
    @24
    @31
    @33
    mplsubglem.r
    ad2antrr
    #
    @32
    @3
    cB
    wcel
    #
    @33
    @32
    @40
    @3
    c.0
    csupp
    co
    #
    cA
    wcel
    #
    wph
    @31
    @40
    @42
    wa
    #
    wph
    @31
    @3
    @17
    wcel
    @43
    wph
    cU
    @17
    @3
    mplsubglem.u
    eleq2d
    @16
    @42
    vg
    @3
    cB
    vg
    vu
    weq
    @15
    @41
    cA
    @14
    @3
    c.0
    csupp
    oveq1
    eleq1d
    elrab
    syl6bb
    biimpa
    #
    simpld
    #
    adantr
    #
    @34
    @4
    cB
    wcel
    #
    @4
    c.0
    csupp
    co
    #
    cA
    wcel
    #
    @32
    @33
    @47
    @49
    wa
    #
    @32
    @33
    @4
    @17
    wcel
    @50
    @32
    cU
    @17
    @4
    wph
    cU
    @17
    wceq
    #
    @31
    mplsubglem.u
    adantr
    #
    eleq2d
    @16
    @49
    vg
    @4
    cB
    vg
    vv
    weq
    @15
    @48
    cA
    @14
    @4
    c.0
    csupp
    oveq1
    eleq1d
    elrab
    syl6bb
    biimpa
    #
    simpld
    #
    psraddcl
    #
    @34
    @36
    cvv
    wcel
    vy
    cv
    #
    @41
    @48
    cun
    #
    wss
    #
    @56
    cA
    wcel
    #
    wi
    #
    vy
    wal
    #
    @36
    @57
    wss
    #
    @37
    @34
    @6
    c.0
    csupp
    ovexd
    @34
    @57
    cA
    wcel
    #
    @56
    vx
    cv
    #
    wss
    #
    @59
    wi
    #
    vy
    wal
    #
    vx
    cA
    wral
    #
    @61
    @34
    @42
    @49
    @64
    @56
    cun
    #
    cA
    wcel
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @63
    @32
    @42
    @33
    @32
    @40
    @42
    @44
    simprd
    #
    adantr
    @34
    @47
    @49
    @53
    simprd
    wph
    @71
    @31
    @33
    wph
    @70
    vx
    vy
    cA
    cA
    mplsubglem.a
    ralrimivva
    ad2antrr
    @70
    @63
    @41
    @56
    cun
    #
    cA
    wcel
    vx
    vy
    @41
    @48
    cA
    cA
    @64
    @41
    wceq
    #
    @69
    @73
    cA
    @64
    @41
    @56
    uneq1
    eleq1d
    @56
    @48
    wceq
    @73
    @57
    cA
    @56
    @48
    @41
    uneq2
    eleq1d
    rspc2va
    syl21anc
    wph
    @68
    @31
    @33
    wph
    @67
    vx
    cA
    wph
    @64
    cA
    wcel
    #
    wa
    @66
    vy
    wph
    @75
    @65
    @59
    mplsubglem.y
    expr
    alrimiv
    ralrimiva
    #
    ad2antrr
    @67
    @61
    vx
    @57
    cA
    @64
    @57
    wceq
    #
    @66
    @60
    vy
    @77
    @65
    @58
    @59
    @64
    @57
    @56
    sseq2
    imbi1d
    albidv
    rspcv
    sylc
    @34
    cD
    @23
    vk
    @6
    @57
    c.0
    @34
    cB
    cD
    cR
    cS
    vf
    cI
    @23
    @6
    mplsubglem.s
    @26
    mplsubglem.d
    mplsubglem.b
    @55
    psrelbas
    @34
    vk
    cv
    #
    cD
    @57
    cdif
    #
    wcel
    #
    wa
    #
    @78
    @6
    cfv
    #
    @78
    @3
    @4
    cR
    cplusg
    cfv
    #
    cof
    co
    #
    cfv
    #
    @78
    @3
    cfv
    #
    @78
    @4
    cfv
    #
    @83
    co
    #
    c.0
    @34
    @82
    @85
    wceq
    @80
    @34
    @78
    @6
    @84
    @34
    cB
    @83
    @5
    cR
    cS
    cI
    @3
    @4
    mplsubglem.s
    mplsubglem.b
    @83
    eqid
    #
    @38
    @46
    @54
    psradd
    fveq1d
    adantr
    @80
    @34
    @78
    cD
    wcel
    #
    @85
    @88
    wceq
    @78
    cD
    @57
    eldifi
    @34
    cD
    cD
    @86
    @87
    @83
    cD
    @3
    @4
    cvv
    cvv
    @78
    @34
    cD
    @23
    @3
    @32
    cD
    @23
    @3
    wf
    #
    @33
    @32
    cB
    cD
    cR
    cS
    vf
    cI
    @23
    @3
    mplsubglem.s
    @26
    mplsubglem.d
    mplsubglem.b
    @45
    psrelbas
    #
    adantr
    ffnd
    @34
    cD
    @23
    @4
    @34
    cB
    cD
    cR
    cS
    vf
    cI
    @23
    @4
    mplsubglem.s
    @26
    mplsubglem.d
    mplsubglem.b
    @54
    psrelbas
    #
    ffnd
    cD
    cvv
    wcel
    #
    @34
    vf
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    vf
    cn0
    cI
    cmap
    co
    cD
    mplsubglem.d
    cn0
    cI
    cmap
    ovex
    rabex2
    #
    a1i
    #
    @96
    cD
    inidm
    @34
    @90
    wa
    #
    @86
    eqidd
    @97
    @87
    eqidd
    ofval
    sylan2
    @81
    @88
    c.0
    c.0
    @83
    co
    #
    c.0
    @81
    @86
    c.0
    @87
    c.0
    @83
    @80
    @34
    @78
    cD
    @41
    cdif
    #
    wcel
    #
    @86
    c.0
    wceq
    #
    @79
    @99
    @78
    @41
    @57
    wss
    @79
    @99
    wss
    @41
    @48
    ssun1
    @41
    @57
    cD
    sscon
    ax-mp
    sseli
    @32
    @100
    @101
    @33
    @32
    cD
    @23
    cvv
    @3
    cvv
    @41
    @78
    c.0
    @92
    @41
    @41
    wss
    @32
    @41
    ssid
    a1i
    @94
    @32
    @95
    a1i
    c.0
    cvv
    wcel
    #
    @32
    @30
    a1i
    suppssr
    #
    adantlr
    sylan2
    @80
    @34
    @78
    cD
    @48
    cdif
    #
    wcel
    @87
    c.0
    wceq
    @79
    @104
    @78
    @48
    @57
    wss
    @79
    @104
    wss
    @48
    @41
    ssun2
    @48
    @57
    cD
    sscon
    ax-mp
    sseli
    @34
    cD
    @23
    cvv
    @4
    cvv
    @48
    @78
    c.0
    @93
    @48
    @48
    wss
    @34
    @48
    ssid
    a1i
    @96
    @102
    @34
    @30
    a1i
    suppssr
    sylan2
    oveq12d
    @34
    @98
    c.0
    wceq
    #
    @80
    @34
    @24
    @105
    @39
    @24
    @25
    @105
    @27
    @23
    @83
    cR
    c.0
    c.0
    @26
    @89
    mplsubglem.z
    grplid
    mpdan
    syl
    adantr
    eqtrd
    3eqtrd
    suppss
    @60
    @62
    @37
    wi
    vy
    @36
    cvv
    @56
    @36
    wceq
    @58
    @62
    @59
    @37
    @56
    @36
    @57
    sseq1
    @56
    @36
    cA
    eleq1
    imbi12d
    spcgv
    syl3c
    @34
    @7
    @6
    @17
    wcel
    @35
    @37
    wa
    @34
    cU
    @17
    @6
    wph
    @51
    @31
    @33
    mplsubglem.u
    ad2antrr
    eleq2d
    @16
    @37
    vg
    @6
    cB
    @14
    @6
    wceq
    @15
    @36
    cA
    @14
    @6
    c.0
    csupp
    oveq1
    eleq1d
    elrab
    syl6bb
    mpbir2and
    ralrimiva
    @32
    @11
    @10
    cB
    wcel
    #
    @10
    c.0
    csupp
    co
    #
    cA
    wcel
    #
    wph
    cS
    cgrp
    wcel
    #
    @31
    @40
    @106
    wph
    cR
    cS
    cI
    cW
    mplsubglem.s
    mplsubglem.i
    mplsubglem.r
    psrgrp
    #
    @45
    cB
    cS
    @9
    @3
    mplsubglem.b
    @9
    eqid
    #
    grpinvcl
    syl2an2r
    #
    @32
    @107
    cvv
    wcel
    @56
    @41
    wss
    #
    @59
    wi
    #
    vy
    wal
    #
    @107
    @41
    wss
    #
    @108
    @32
    @10
    c.0
    csupp
    ovexd
    @32
    @42
    @68
    @115
    @72
    wph
    @68
    @31
    @76
    adantr
    @67
    @115
    vx
    @41
    cA
    @74
    @66
    @114
    vy
    @74
    @65
    @113
    @59
    @64
    @41
    @56
    sseq2
    imbi1d
    albidv
    rspcv
    sylc
    @32
    cD
    @23
    vk
    @10
    @41
    c.0
    @32
    cB
    cD
    cR
    cS
    vf
    cI
    @23
    @10
    mplsubglem.s
    @26
    mplsubglem.d
    mplsubglem.b
    @112
    psrelbas
    @32
    @100
    wa
    #
    @78
    @10
    cfv
    @78
    cR
    cminusg
    cfv
    #
    @3
    ccom
    #
    cfv
    #
    @86
    @118
    cfv
    #
    c.0
    @117
    @78
    @10
    @119
    @32
    @10
    @119
    wceq
    @100
    @32
    cB
    cD
    cR
    cS
    vf
    cI
    @9
    @118
    cW
    @3
    mplsubglem.s
    wph
    cI
    cW
    wcel
    @31
    mplsubglem.i
    adantr
    wph
    @24
    @31
    mplsubglem.r
    adantr
    #
    mplsubglem.d
    @118
    eqid
    #
    mplsubglem.b
    @111
    @45
    psrneg
    adantr
    fveq1d
    @32
    @91
    @90
    @120
    @121
    wceq
    @100
    @92
    @78
    cD
    @41
    eldifi
    cD
    @23
    @78
    @118
    @3
    fvco3
    syl2an
    @117
    @121
    c.0
    @118
    cfv
    #
    c.0
    @117
    @86
    c.0
    @118
    @103
    fveq2d
    @32
    @124
    c.0
    wceq
    #
    @100
    @32
    @24
    @125
    @122
    cR
    @118
    c.0
    mplsubglem.z
    @123
    grpinvid
    syl
    adantr
    eqtrd
    3eqtrd
    suppss
    @114
    @116
    @108
    wi
    vy
    @107
    cvv
    @56
    @107
    wceq
    @113
    @116
    @59
    @108
    @56
    @107
    @41
    sseq1
    @56
    @107
    cA
    eleq1
    imbi12d
    spcgv
    syl3c
    @32
    @11
    @10
    @17
    wcel
    @106
    @108
    wa
    @32
    cU
    @17
    @10
    @52
    eleq2d
    @16
    @108
    vg
    @10
    cB
    @14
    @10
    wceq
    @15
    @107
    cA
    @14
    @10
    c.0
    csupp
    oveq1
    eleq1d
    elrab
    syl6bb
    mpbir2and
    jca
    ralrimiva
    wph
    @109
    @0
    @1
    @2
    @13
    w3a
    wb
    @110
    vu
    vv
    cB
    @5
    cU
    cS
    @9
    mplsubglem.b
    @38
    @111
    issubg2
    syl
    mpbir3and
end
