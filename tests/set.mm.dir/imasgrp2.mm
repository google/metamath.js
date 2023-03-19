include "cgrp.mm"
include "wcel.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "cplusg.mm"
include "imasbas.mm"
include "eqidd.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wa.mm"
include "w3a.mm"
include "wb.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "3ad2ant1.mm"
include "sylibd.mm"
include "eqid.mm"
include "adantr.mm"
include "3expb.mm"
include "caovclg.mm"
include "eqeltrrd.mm"
include "imasaddf.mm"
include "fovrn.mm"
include "syl3an1.mm"
include "wrex.mm"
include "crn.mm"
include "wfo.mm"
include "forn.mm"
include "syl.mm"
include "eleq2d.mm"
include "3anbi123d.mm"
include "wfn.mm"
include "fofn.mm"
include "fvelrnb.mm"
include "bitr3d.mm"
include "3reeanv.mm"
include "syl6bbr.mm"
include "wi.mm"
include "3eqtr3d.mm"
include "simpl.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "imasaddval.mm"
include "syl3anc.mm"
include "simpr1.mm"
include "3adantr1.mm"
include "3eqtr4d.mm"
include "eqtr4d.mm"
include "oveq1d.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "simp1.mm"
include "simp2.mm"
include "oveq12d.mm"
include "simp3.mm"
include "syl5ibcom.mm"
include "3exp2.mm"
include "imp32.mm"
include "rexlimdv.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "imp.mm"
include "fof.mm"
include "ffvelrnd.mm"
include "simpr.mm"
include "3eqtr2d.mm"
include "oveq2.mm"
include "id.mm"
include "rexlimdva.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexbidv.mm"
include "isgrpde.mm"
include "grpidd2.mm"
include "jca.mm"

theorem imasgrp2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cU: class U
  let cF: class F
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume imasgrp.u: |- ( ph -> U = ( F "s R ) )
  assume imasgrp.v: |- ( ph -> V = ( Base ` R ) )
  assume imasgrp.p: |- ( ph -> .+ = ( +g ` R ) )
  assume imasgrp.f: |- ( ph -> F : V -onto-> B )
  assume imasgrp.e: |- ( ( ph /\ ( a e. V /\ b e. V ) /\ ( p e. V /\ q e. V ) ) -> ( ( ( F ` a ) = ( F ` p ) /\ ( F ` b ) = ( F ` q ) ) -> ( F ` ( a .+ b ) ) = ( F ` ( p .+ q ) ) ) )
  assume imasgrp2.r: |- ( ph -> R e. W )
  assume imasgrp2.1: |- ( ( ph /\ x e. V /\ y e. V ) -> ( x .+ y ) e. V )
  assume imasgrp2.2: |- ( ( ph /\ ( x e. V /\ y e. V /\ z e. V ) ) -> ( F ` ( ( x .+ y ) .+ z ) ) = ( F ` ( x .+ ( y .+ z ) ) ) )
  assume imasgrp2.3: |- ( ph -> .0. e. V )
  assume imasgrp2.4: |- ( ( ph /\ x e. V ) -> ( F ` ( .0. .+ x ) ) = ( F ` x ) )
  assume imasgrp2.5: |- ( ( ph /\ x e. V ) -> N e. V )
  assume imasgrp2.6: |- ( ( ph /\ x e. V ) -> ( F ` ( N .+ x ) ) = ( F ` .0. ) )

  disjoint p q
  disjoint p x
  disjoint B p
  disjoint q x
  disjoint B q
  disjoint B x
  disjoint N p
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint a ph
  disjoint b p
  disjoint b q
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint b ph
  disjoint p y
  disjoint p z
  disjoint p ph
  disjoint q y
  disjoint q z
  disjoint ph q
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint R p
  disjoint R q
  disjoint F a
  disjoint F b
  disjoint F p
  disjoint F q
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint .+ p
  disjoint .+ q
  disjoint .+ x
  disjoint .+ y
  disjoint U a
  disjoint U b
  disjoint U p
  disjoint U q
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint V a
  disjoint V b
  disjoint V p
  disjoint V q
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint .0. p
  disjoint .0. q
  disjoint .0. x
  disjoint p u
  disjoint p v
  disjoint p w
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint B u
  disjoint v w
  disjoint v x
  disjoint B v
  disjoint w x
  disjoint B w
  disjoint N v
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint u y
  disjoint u z
  disjoint ph u
  disjoint v y
  disjoint v z
  disjoint ph v
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint F u
  disjoint F v
  disjoint F w
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint .0. u
  disjoint .0. v
  disjoint .0. w
  assert |- ( ph -> ( U e. Grp /\ ( F ` .0. ) = ( 0g ` U ) ) )

  proof
    wph
    cU
    cgrp
    wcel
    c.0
    cF
    cfv
    #
    cU
    c0g
    cfv
    wceq
    wph
    vu
    vv
    vw
    cB
    cU
    cplusg
    cfv
    #
    cU
    @0
    wph
    cB
    cR
    cU
    cF
    cV
    cW
    imasgrp.u
    imasgrp.v
    imasgrp.f
    imasgrp2.r
    imasbas
    #
    wph
    @1
    eqidd
    #
    wph
    cB
    cB
    cxp
    cB
    @1
    wf
    vu
    cv
    #
    cB
    wcel
    #
    vv
    cv
    #
    cB
    wcel
    #
    @4
    @6
    @1
    co
    #
    cB
    wcel
    wph
    cB
    cR
    @1
    cR
    cplusg
    cfv
    #
    cU
    cF
    cV
    cW
    vq
    vp
    va
    vb
    imasgrp.f
    wph
    va
    cv
    #
    cV
    wcel
    vb
    cv
    #
    cV
    wcel
    wa
    #
    vp
    cv
    #
    cV
    wcel
    vq
    cv
    #
    cV
    wcel
    wa
    #
    w3a
    @10
    cF
    cfv
    @13
    cF
    cfv
    wceq
    @11
    cF
    cfv
    @14
    cF
    cfv
    wceq
    wa
    @10
    @11
    c.pl
    co
    #
    cF
    cfv
    #
    @13
    @14
    c.pl
    co
    #
    cF
    cfv
    #
    wceq
    #
    @10
    @11
    @9
    co
    #
    cF
    cfv
    #
    @13
    @14
    @9
    co
    #
    cF
    cfv
    #
    wceq
    #
    imasgrp.e
    wph
    @12
    @20
    @25
    wb
    @15
    wph
    @17
    @22
    @19
    @24
    wph
    @16
    @21
    cF
    wph
    c.pl
    @9
    @10
    @11
    imasgrp.p
    oveqd
    fveq2d
    wph
    @18
    @23
    cF
    wph
    c.pl
    @9
    @13
    @14
    imasgrp.p
    oveqd
    #
    fveq2d
    eqeq12d
    3ad2ant1
    sylibd
    #
    imasgrp.u
    imasgrp.v
    imasgrp2.r
    @9
    eqid
    #
    @1
    eqid
    #
    wph
    @15
    wa
    @18
    @23
    cV
    wph
    @18
    @23
    wceq
    @15
    @26
    adantr
    wph
    vx
    vy
    @13
    @14
    cV
    cV
    cV
    c.pl
    wph
    vx
    cv
    #
    cV
    wcel
    #
    vy
    cv
    #
    cV
    wcel
    #
    @30
    @32
    c.pl
    co
    #
    cV
    wcel
    #
    imasgrp2.1
    3expb
    caovclg
    #
    eqeltrrd
    imasaddf
    @4
    @6
    cB
    cB
    cB
    @1
    fovrn
    syl3an1
    wph
    @5
    @7
    vw
    cv
    #
    cB
    wcel
    #
    w3a
    #
    @8
    @37
    @1
    co
    #
    @4
    @6
    @37
    @1
    co
    #
    @1
    co
    #
    wceq
    #
    wph
    @39
    @30
    cF
    cfv
    #
    @4
    wceq
    #
    @32
    cF
    cfv
    #
    @6
    wceq
    #
    vz
    cv
    #
    cF
    cfv
    #
    @37
    wceq
    #
    w3a
    #
    vz
    cV
    wrex
    #
    vy
    cV
    wrex
    vx
    cV
    wrex
    #
    @43
    wph
    @39
    @45
    vx
    cV
    wrex
    #
    @47
    vy
    cV
    wrex
    #
    @50
    vz
    cV
    wrex
    #
    w3a
    #
    @53
    wph
    @4
    cF
    crn
    #
    wcel
    #
    @6
    @58
    wcel
    #
    @37
    @58
    wcel
    #
    w3a
    #
    @39
    @57
    wph
    @59
    @5
    @60
    @7
    @61
    @38
    wph
    @58
    cB
    @4
    wph
    cV
    cB
    cF
    wfo
    #
    @58
    cB
    wceq
    imasgrp.f
    cV
    cB
    cF
    forn
    syl
    #
    eleq2d
    #
    wph
    @58
    cB
    @6
    @64
    eleq2d
    wph
    @58
    cB
    @37
    @64
    eleq2d
    3anbi123d
    wph
    cF
    cV
    wfn
    #
    @62
    @57
    wb
    wph
    @63
    @66
    imasgrp.f
    cV
    cB
    cF
    fofn
    syl
    #
    @66
    @59
    @54
    @60
    @55
    @61
    @56
    vx
    cV
    @4
    cF
    fvelrnb
    #
    vy
    cV
    @6
    cF
    fvelrnb
    vz
    cV
    @37
    cF
    fvelrnb
    3anbi123d
    syl
    bitr3d
    @45
    @47
    @50
    vx
    vy
    vz
    cV
    cV
    cV
    3reeanv
    syl6bbr
    wph
    @52
    @43
    vx
    vy
    cV
    cV
    wph
    @31
    @33
    wa
    wa
    @51
    @43
    vz
    cV
    wph
    @31
    @33
    @48
    cV
    wcel
    #
    @51
    @43
    wi
    #
    wi
    wph
    @31
    @33
    @69
    @70
    wph
    @31
    @33
    @69
    w3a
    #
    wa
    #
    @44
    @46
    @1
    co
    #
    @49
    @1
    co
    #
    @44
    @46
    @49
    @1
    co
    #
    @1
    co
    #
    wceq
    @51
    @43
    @72
    @34
    cF
    cfv
    #
    @49
    @1
    co
    #
    @44
    @32
    @48
    c.pl
    co
    #
    cF
    cfv
    #
    @1
    co
    #
    @74
    @76
    @72
    @34
    @48
    @9
    co
    #
    cF
    cfv
    #
    @30
    @79
    @9
    co
    #
    cF
    cfv
    #
    @78
    @81
    @72
    @34
    @48
    c.pl
    co
    #
    cF
    cfv
    @30
    @79
    c.pl
    co
    #
    cF
    cfv
    @83
    @85
    imasgrp2.2
    @72
    @86
    @82
    cF
    @72
    c.pl
    @9
    @34
    @48
    wph
    c.pl
    @9
    wceq
    #
    @71
    imasgrp.p
    adantr
    #
    oveqd
    fveq2d
    @72
    @87
    @84
    cF
    @72
    c.pl
    @9
    @30
    @79
    @89
    oveqd
    fveq2d
    3eqtr3d
    @72
    wph
    @35
    @69
    @78
    @83
    wceq
    wph
    @71
    simpl
    #
    wph
    @31
    @33
    @35
    @69
    imasgrp2.1
    3adant3r3
    wph
    @31
    @33
    @69
    simpr3
    wph
    cB
    cR
    @1
    @9
    cU
    cF
    cV
    @34
    @48
    cW
    vq
    vp
    va
    vb
    imasgrp.f
    @27
    imasgrp.u
    imasgrp.v
    imasgrp2.r
    @28
    @29
    imasaddval
    syl3anc
    @72
    wph
    @31
    @79
    cV
    wcel
    #
    @81
    @85
    wceq
    @90
    wph
    @31
    @33
    @69
    simpr1
    wph
    @33
    @69
    @91
    @31
    wph
    vp
    vq
    @32
    @48
    cV
    cV
    cV
    c.pl
    @36
    caovclg
    3adantr1
    wph
    cB
    cR
    @1
    @9
    cU
    cF
    cV
    @30
    @79
    cW
    vq
    vp
    va
    vb
    imasgrp.f
    @27
    imasgrp.u
    imasgrp.v
    imasgrp2.r
    @28
    @29
    imasaddval
    syl3anc
    3eqtr4d
    @72
    @73
    @77
    @49
    @1
    @72
    @73
    @30
    @32
    @9
    co
    #
    cF
    cfv
    #
    @77
    wph
    @31
    @33
    @73
    @93
    wceq
    @69
    wph
    cB
    cR
    @1
    @9
    cU
    cF
    cV
    @30
    @32
    cW
    vq
    vp
    va
    vb
    imasgrp.f
    @27
    imasgrp.u
    imasgrp.v
    imasgrp2.r
    @28
    @29
    imasaddval
    3adant3r3
    @72
    @34
    @92
    cF
    @72
    c.pl
    @9
    @30
    @32
    @89
    oveqd
    fveq2d
    eqtr4d
    oveq1d
    @72
    @75
    @80
    @44
    @1
    @72
    @75
    @32
    @48
    @9
    co
    #
    cF
    cfv
    #
    @80
    wph
    @33
    @69
    @75
    @95
    wceq
    @31
    wph
    cB
    cR
    @1
    @9
    cU
    cF
    cV
    @32
    @48
    cW
    vq
    vp
    va
    vb
    imasgrp.f
    @27
    imasgrp.u
    imasgrp.v
    imasgrp2.r
    @28
    @29
    imasaddval
    3adant3r1
    @72
    @79
    @94
    cF
    @72
    c.pl
    @9
    @32
    @48
    @89
    oveqd
    fveq2d
    eqtr4d
    oveq2d
    3eqtr4d
    @51
    @74
    @40
    @76
    @42
    @51
    @73
    @8
    @49
    @37
    @1
    @51
    @44
    @4
    @46
    @6
    @1
    @45
    @47
    @50
    simp1
    #
    @45
    @47
    @50
    simp2
    #
    oveq12d
    @45
    @47
    @50
    simp3
    #
    oveq12d
    @51
    @44
    @4
    @75
    @41
    @1
    @96
    @51
    @46
    @6
    @49
    @37
    @1
    @97
    @98
    oveq12d
    oveq12d
    eqeq12d
    syl5ibcom
    3exp2
    imp32
    rexlimdv
    rexlimdvva
    sylbid
    imp
    wph
    cV
    cB
    c.0
    cF
    wph
    @63
    cV
    cB
    cF
    wf
    #
    imasgrp.f
    cV
    cB
    cF
    fof
    syl
    #
    imasgrp2.3
    ffvelrnd
    #
    wph
    @5
    @0
    @4
    @1
    co
    #
    @4
    wceq
    #
    wph
    @5
    @54
    @103
    wph
    @59
    @5
    @54
    @65
    wph
    @66
    @59
    @54
    wb
    @67
    @68
    syl
    bitr3d
    #
    wph
    @45
    @103
    vx
    cV
    wph
    @31
    wa
    #
    @0
    @44
    @1
    co
    #
    @44
    wceq
    @45
    @103
    @105
    @106
    c.0
    @30
    @9
    co
    #
    cF
    cfv
    #
    c.0
    @30
    c.pl
    co
    #
    cF
    cfv
    @44
    @105
    wph
    c.0
    cV
    wcel
    #
    @31
    @106
    @108
    wceq
    wph
    @31
    simpl
    #
    wph
    @110
    @31
    imasgrp2.3
    adantr
    wph
    @31
    simpr
    #
    wph
    cB
    cR
    @1
    @9
    cU
    cF
    cV
    c.0
    @30
    cW
    vq
    vp
    va
    vb
    imasgrp.f
    @27
    imasgrp.u
    imasgrp.v
    imasgrp2.r
    @28
    @29
    imasaddval
    syl3anc
    @105
    @109
    @107
    cF
    @105
    c.pl
    @9
    c.0
    @30
    wph
    @88
    @31
    imasgrp.p
    adantr
    #
    oveqd
    fveq2d
    imasgrp2.4
    3eqtr2d
    @45
    @106
    @102
    @44
    @4
    @44
    @4
    @0
    @1
    oveq2
    @45
    id
    eqeq12d
    syl5ibcom
    rexlimdva
    sylbid
    imp
    #
    wph
    @5
    @6
    @4
    @1
    co
    #
    @0
    wceq
    #
    vv
    cB
    wrex
    #
    wph
    @5
    @54
    @117
    @104
    wph
    @45
    @117
    vx
    cV
    @105
    @6
    @44
    @1
    co
    #
    @0
    wceq
    #
    vv
    cB
    wrex
    #
    @45
    @117
    @105
    cN
    cF
    cfv
    #
    cB
    wcel
    @121
    @44
    @1
    co
    #
    @0
    wceq
    #
    @120
    @105
    cV
    cB
    cN
    cF
    wph
    @99
    @31
    @100
    adantr
    imasgrp2.5
    ffvelrnd
    @105
    @122
    cN
    @30
    @9
    co
    #
    cF
    cfv
    #
    cN
    @30
    c.pl
    co
    #
    cF
    cfv
    @0
    @105
    wph
    cN
    cV
    wcel
    @31
    @122
    @125
    wceq
    @111
    imasgrp2.5
    @112
    wph
    cB
    cR
    @1
    @9
    cU
    cF
    cV
    cN
    @30
    cW
    vq
    vp
    va
    vb
    imasgrp.f
    @27
    imasgrp.u
    imasgrp.v
    imasgrp2.r
    @28
    @29
    imasaddval
    syl3anc
    @105
    @126
    @124
    cF
    @105
    c.pl
    @9
    cN
    @30
    @113
    oveqd
    fveq2d
    imasgrp2.6
    3eqtr2d
    @119
    @123
    vv
    @121
    cB
    @6
    @121
    wceq
    @118
    @122
    @0
    @6
    @121
    @44
    @1
    oveq1
    eqeq1d
    rspcev
    syl2anc
    @45
    @119
    @116
    vv
    cB
    @45
    @118
    @115
    @0
    @44
    @4
    @6
    @1
    oveq2
    eqeq1d
    rexbidv
    syl5ibcom
    rexlimdva
    sylbid
    imp
    isgrpde
    #
    wph
    vu
    cB
    @1
    cU
    @0
    @2
    @3
    @101
    @114
    @127
    grpidd2
    jca
end
