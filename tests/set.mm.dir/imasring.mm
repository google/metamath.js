include "crg.mm"
include "wcel.mm"
include "cfv.mm"
include "cur.mm"
include "wceq.mm"
include "cplusg.mm"
include "cmulr.mm"
include "imasbas.mm"
include "eqidd.mm"
include "cgrp.mm"
include "c0g.mm"
include "a1i.mm"
include "ringgrp.mm"
include "syl.mm"
include "eqid.mm"
include "imasgrp.mm"
include "simpld.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wa.mm"
include "cbs.mm"
include "adantr.mm"
include "simprl.mm"
include "eleqtrd.mm"
include "simprr.mm"
include "ringcl.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"
include "caovclg.mm"
include "imasmulf.mm"
include "fovrn.mm"
include "syl3an1.mm"
include "w3a.mm"
include "wrex.mm"
include "crn.mm"
include "wfo.mm"
include "forn.mm"
include "eleq2d.mm"
include "3anbi123d.mm"
include "wfn.mm"
include "wb.mm"
include "fofn.mm"
include "fvelrnb.mm"
include "bitr3d.mm"
include "3reeanv.mm"
include "syl6bbr.mm"
include "wi.mm"
include "simp2.mm"
include "3ad2ant1.mm"
include "3adant3r3.mm"
include "simp3.mm"
include "simpr3.mm"
include "ringass.mm"
include "syl13anc.mm"
include "fveq2d.mm"
include "simpl.mm"
include "3adantr3.mm"
include "imasmulval.mm"
include "simpr1.mm"
include "3adantr1.mm"
include "3eqtr4d.mm"
include "oveq1d.mm"
include "3adant3r1.mm"
include "oveq2d.mm"
include "simp1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "syl5ibcom.mm"
include "3exp2.mm"
include "imp32.mm"
include "rexlimdv.mm"
include "rexlimdvva.mm"
include "sylbid.mm"
include "imp.mm"
include "ringdi.mm"
include "ringacl.mm"
include "3adantr2.mm"
include "imasaddval.mm"
include "3adant3r2.mm"
include "ringdir.mm"
include "fof.mm"
include "ringidcl.mm"
include "ffvelrnd.mm"
include "simpr.mm"
include "biimpa.mm"
include "ringlidm.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "oveq2.mm"
include "id.mm"
include "rexlimdva.mm"
include "mpd3an3.mm"
include "ringridm.mm"
include "oveq1.mm"
include "isringd.mm"
include "wral.mm"
include "jcad.mm"
include "sylbird.mm"
include "ralrimiv.mm"
include "isringid.mm"
include "mpbi2and.mm"
include "eqcomd.mm"
include "jca.mm"

theorem imasring
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let cF: class F
  let cV: class V
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume imasring.u: |- ( ph -> U = ( F "s R ) )
  assume imasring.v: |- ( ph -> V = ( Base ` R ) )
  assume imasring.p: |- .+ = ( +g ` R )
  assume imasring.t: |- .x. = ( .r ` R )
  assume imasring.o: |- .1. = ( 1r ` R )
  assume imasring.f: |- ( ph -> F : V -onto-> B )
  assume imasring.e1: |- ( ( ph /\ ( a e. V /\ b e. V ) /\ ( p e. V /\ q e. V ) ) -> ( ( ( F ` a ) = ( F ` p ) /\ ( F ` b ) = ( F ` q ) ) -> ( F ` ( a .+ b ) ) = ( F ` ( p .+ q ) ) ) )
  assume imasring.e2: |- ( ( ph /\ ( a e. V /\ b e. V ) /\ ( p e. V /\ q e. V ) ) -> ( ( ( F ` a ) = ( F ` p ) /\ ( F ` b ) = ( F ` q ) ) -> ( F ` ( a .x. b ) ) = ( F ` ( p .x. q ) ) ) )
  assume imasring.r: |- ( ph -> R e. Ring )

  disjoint p q
  disjoint .+ p
  disjoint .+ q
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a ph
  disjoint b p
  disjoint b q
  disjoint b ph
  disjoint p ph
  disjoint ph q
  disjoint U a
  disjoint U b
  disjoint U p
  disjoint U q
  disjoint .1. p
  disjoint .1. q
  disjoint B p
  disjoint B q
  disjoint F a
  disjoint F b
  disjoint F p
  disjoint F q
  disjoint R p
  disjoint R q
  disjoint V a
  disjoint V b
  disjoint V p
  disjoint V q
  disjoint .x. p
  disjoint .x. q
  disjoint p u
  disjoint p v
  disjoint q u
  disjoint q v
  disjoint u v
  disjoint .+ u
  disjoint .+ v
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint ph u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint x y
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint .1. u
  disjoint .1. x
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint V u
  disjoint V v
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint .x. u
  disjoint .x. v
  assert |- ( ph -> ( U e. Ring /\ ( F ` .1. ) = ( 1r ` U ) ) )

  proof
    wph
    cU
    crg
    wcel
    #
    c.1
    cF
    cfv
    #
    cU
    cur
    cfv
    #
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
    cU
    cmulr
    cfv
    #
    @1
    wph
    cB
    cR
    cU
    cF
    cV
    crg
    imasring.u
    imasring.v
    imasring.f
    imasring.r
    imasbas
    #
    wph
    @3
    eqidd
    wph
    @4
    eqidd
    wph
    cU
    cgrp
    wcel
    cR
    c0g
    cfv
    #
    cF
    cfv
    cU
    c0g
    cfv
    wceq
    wph
    cB
    c.pl
    cR
    cU
    cF
    cV
    @6
    vq
    vp
    va
    vb
    imasring.u
    imasring.v
    c.pl
    cR
    cplusg
    cfv
    wceq
    wph
    imasring.p
    a1i
    imasring.f
    imasring.e1
    wph
    cR
    crg
    wcel
    #
    cR
    cgrp
    wcel
    imasring.r
    cR
    ringgrp
    syl
    @6
    eqid
    imasgrp
    simpld
    wph
    cB
    cB
    cxp
    cB
    @4
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
    @8
    @10
    @4
    co
    #
    cB
    wcel
    wph
    cB
    cR
    @4
    c.x
    cU
    cF
    cV
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e2
    imasring.u
    imasring.v
    imasring.r
    imasring.t
    @4
    eqid
    #
    wph
    vu
    vv
    vp
    cv
    vq
    cv
    cV
    cV
    cV
    c.x
    wph
    @8
    cV
    wcel
    #
    @10
    cV
    wcel
    #
    wa
    #
    wa
    #
    @8
    @10
    c.x
    co
    #
    cR
    cbs
    cfv
    #
    cV
    @17
    @7
    @8
    @19
    wcel
    #
    @10
    @19
    wcel
    #
    @18
    @19
    wcel
    wph
    @7
    @16
    imasring.r
    adantr
    #
    @17
    @8
    cV
    @19
    wph
    @14
    @15
    simprl
    wph
    cV
    @19
    wceq
    #
    @16
    imasring.v
    adantr
    #
    eleqtrd
    #
    @17
    @10
    cV
    @19
    wph
    @14
    @15
    simprr
    @24
    eleqtrd
    #
    @19
    cR
    c.x
    @8
    @10
    @19
    eqid
    #
    imasring.t
    ringcl
    syl3anc
    @24
    eleqtrrd
    #
    caovclg
    imasmulf
    @8
    @10
    cB
    cB
    cB
    @4
    fovrn
    syl3an1
    wph
    @9
    @11
    vw
    cv
    #
    cB
    wcel
    #
    w3a
    #
    @12
    @29
    @4
    co
    #
    @8
    @10
    @29
    @4
    co
    #
    @4
    co
    #
    wceq
    #
    wph
    @31
    vx
    cv
    #
    cF
    cfv
    #
    @8
    wceq
    #
    vy
    cv
    #
    cF
    cfv
    #
    @10
    wceq
    #
    vz
    cv
    #
    cF
    cfv
    #
    @29
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
    @35
    wph
    @31
    @38
    vx
    cV
    wrex
    #
    @41
    vy
    cV
    wrex
    #
    @44
    vz
    cV
    wrex
    #
    w3a
    #
    @47
    wph
    @8
    cF
    crn
    #
    wcel
    #
    @10
    @52
    wcel
    #
    @29
    @52
    wcel
    #
    w3a
    #
    @31
    @51
    wph
    @53
    @9
    @54
    @11
    @55
    @30
    wph
    @52
    cB
    @8
    wph
    cV
    cB
    cF
    wfo
    #
    @52
    cB
    wceq
    imasring.f
    cV
    cB
    cF
    forn
    syl
    #
    eleq2d
    #
    wph
    @52
    cB
    @10
    @58
    eleq2d
    wph
    @52
    cB
    @29
    @58
    eleq2d
    3anbi123d
    wph
    cF
    cV
    wfn
    #
    @56
    @51
    wb
    wph
    @57
    @60
    imasring.f
    cV
    cB
    cF
    fofn
    syl
    #
    @60
    @53
    @48
    @54
    @49
    @55
    @50
    vx
    cV
    @8
    cF
    fvelrnb
    #
    vy
    cV
    @10
    cF
    fvelrnb
    vz
    cV
    @29
    cF
    fvelrnb
    3anbi123d
    syl
    bitr3d
    @38
    @41
    @44
    vx
    vy
    vz
    cV
    cV
    cV
    3reeanv
    syl6bbr
    #
    wph
    @46
    @35
    vx
    vy
    cV
    cV
    wph
    @36
    cV
    wcel
    #
    @39
    cV
    wcel
    #
    wa
    wa
    #
    @45
    @35
    vz
    cV
    wph
    @64
    @65
    @42
    cV
    wcel
    #
    @45
    @35
    wi
    #
    wi
    wph
    @64
    @65
    @67
    @68
    wph
    @64
    @65
    @67
    w3a
    #
    wa
    #
    @37
    @40
    @4
    co
    #
    @43
    @4
    co
    #
    @37
    @40
    @43
    @4
    co
    #
    @4
    co
    #
    wceq
    @45
    @35
    @70
    @36
    @39
    c.x
    co
    #
    cF
    cfv
    #
    @43
    @4
    co
    #
    @37
    @39
    @42
    c.x
    co
    #
    cF
    cfv
    #
    @4
    co
    #
    @72
    @74
    @70
    @75
    @42
    c.x
    co
    #
    cF
    cfv
    #
    @36
    @78
    c.x
    co
    #
    cF
    cfv
    #
    @77
    @80
    @70
    @81
    @83
    cF
    @70
    @7
    @36
    @19
    wcel
    #
    @39
    @19
    wcel
    #
    @42
    @19
    wcel
    #
    @81
    @83
    wceq
    wph
    @7
    @69
    imasring.r
    adantr
    #
    wph
    @64
    @65
    @85
    @67
    wph
    @64
    @65
    w3a
    #
    @36
    cV
    @19
    wph
    @64
    @65
    simp2
    wph
    @64
    @23
    @65
    imasring.v
    3ad2ant1
    #
    eleqtrd
    3adant3r3
    #
    wph
    @64
    @65
    @86
    @67
    @89
    @39
    cV
    @19
    wph
    @64
    @65
    simp3
    @90
    eleqtrd
    3adant3r3
    #
    @70
    @42
    cV
    @19
    wph
    @64
    @65
    @67
    simpr3
    #
    wph
    @23
    @69
    imasring.v
    adantr
    eleqtrd
    #
    @19
    cR
    c.x
    @36
    @39
    @42
    @27
    imasring.t
    ringass
    syl13anc
    fveq2d
    @70
    wph
    @75
    cV
    wcel
    #
    @67
    @77
    @82
    wceq
    wph
    @69
    simpl
    #
    wph
    @64
    @65
    @95
    @67
    wph
    vu
    vv
    @36
    @39
    cV
    cV
    cV
    c.x
    @28
    caovclg
    3adantr3
    #
    @93
    wph
    cB
    cR
    @4
    c.x
    cU
    cF
    cV
    @75
    @42
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e2
    imasring.u
    imasring.v
    imasring.r
    imasring.t
    @13
    imasmulval
    syl3anc
    @70
    wph
    @64
    @78
    cV
    wcel
    #
    @80
    @84
    wceq
    @96
    wph
    @64
    @65
    @67
    simpr1
    #
    wph
    @65
    @67
    @98
    @64
    wph
    vu
    vv
    @39
    @42
    cV
    cV
    cV
    c.x
    @28
    caovclg
    3adantr1
    #
    wph
    cB
    cR
    @4
    c.x
    cU
    cF
    cV
    @36
    @78
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e2
    imasring.u
    imasring.v
    imasring.r
    imasring.t
    @13
    imasmulval
    syl3anc
    3eqtr4d
    @70
    @71
    @76
    @43
    @4
    wph
    @64
    @65
    @71
    @76
    wceq
    @67
    wph
    cB
    cR
    @4
    c.x
    cU
    cF
    cV
    @36
    @39
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e2
    imasring.u
    imasring.v
    imasring.r
    imasring.t
    @13
    imasmulval
    3adant3r3
    #
    oveq1d
    @70
    @73
    @79
    @37
    @4
    wph
    @65
    @67
    @73
    @79
    wceq
    @64
    wph
    cB
    cR
    @4
    c.x
    cU
    cF
    cV
    @39
    @42
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e2
    imasring.u
    imasring.v
    imasring.r
    imasring.t
    @13
    imasmulval
    3adant3r1
    #
    oveq2d
    3eqtr4d
    @45
    @72
    @32
    @74
    @34
    @45
    @71
    @12
    @43
    @29
    @4
    @45
    @37
    @8
    @40
    @10
    @4
    @38
    @41
    @44
    simp1
    #
    @38
    @41
    @44
    simp2
    #
    oveq12d
    #
    @38
    @41
    @44
    simp3
    #
    oveq12d
    @45
    @37
    @8
    @73
    @33
    @4
    @103
    @45
    @40
    @10
    @43
    @29
    @4
    @104
    @106
    oveq12d
    #
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
    @31
    @8
    @10
    @29
    @3
    co
    #
    @4
    co
    #
    @12
    @8
    @29
    @4
    co
    #
    @3
    co
    #
    wceq
    #
    wph
    @31
    @47
    @112
    @63
    wph
    @46
    @112
    vx
    vy
    cV
    cV
    @66
    @45
    @112
    vz
    cV
    wph
    @64
    @65
    @67
    @45
    @112
    wi
    #
    wi
    wph
    @64
    @65
    @67
    @113
    @70
    @37
    @40
    @43
    @3
    co
    #
    @4
    co
    #
    @71
    @37
    @43
    @4
    co
    #
    @3
    co
    #
    wceq
    @45
    @112
    @70
    @37
    @39
    @42
    c.pl
    co
    #
    cF
    cfv
    #
    @4
    co
    #
    @76
    @36
    @42
    c.x
    co
    #
    cF
    cfv
    #
    @3
    co
    #
    @115
    @117
    @70
    @36
    @118
    c.x
    co
    #
    cF
    cfv
    #
    @75
    @121
    c.pl
    co
    #
    cF
    cfv
    #
    @120
    @123
    @70
    @124
    @126
    cF
    @70
    @7
    @85
    @86
    @87
    @124
    @126
    wceq
    @88
    @91
    @92
    @94
    @19
    c.pl
    cR
    c.x
    @36
    @39
    @42
    @27
    imasring.p
    imasring.t
    ringdi
    syl13anc
    fveq2d
    @70
    wph
    @64
    @118
    cV
    wcel
    #
    @120
    @125
    wceq
    @96
    @99
    wph
    @65
    @67
    @128
    @64
    wph
    vu
    vv
    @39
    @42
    cV
    cV
    cV
    c.pl
    @17
    @8
    @10
    c.pl
    co
    #
    @19
    cV
    @17
    @7
    @20
    @21
    @129
    @19
    wcel
    @22
    @25
    @26
    @19
    c.pl
    cR
    @8
    @10
    @27
    imasring.p
    ringacl
    syl3anc
    @24
    eleqtrrd
    #
    caovclg
    3adantr1
    wph
    cB
    cR
    @4
    c.x
    cU
    cF
    cV
    @36
    @118
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e2
    imasring.u
    imasring.v
    imasring.r
    imasring.t
    @13
    imasmulval
    syl3anc
    @70
    wph
    @95
    @121
    cV
    wcel
    #
    @123
    @127
    wceq
    @96
    @97
    wph
    @64
    @67
    @131
    @65
    wph
    vu
    vv
    @36
    @42
    cV
    cV
    cV
    c.x
    @28
    caovclg
    3adantr2
    #
    wph
    cB
    cR
    @3
    c.pl
    cU
    cF
    cV
    @75
    @121
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e1
    imasring.u
    imasring.v
    imasring.r
    imasring.p
    @3
    eqid
    #
    imasaddval
    syl3anc
    3eqtr4d
    @70
    @114
    @119
    @37
    @4
    wph
    @65
    @67
    @114
    @119
    wceq
    @64
    wph
    cB
    cR
    @3
    c.pl
    cU
    cF
    cV
    @39
    @42
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e1
    imasring.u
    imasring.v
    imasring.r
    imasring.p
    @133
    imasaddval
    3adant3r1
    oveq2d
    @70
    @71
    @76
    @116
    @122
    @3
    @101
    wph
    @64
    @67
    @116
    @122
    wceq
    @65
    wph
    cB
    cR
    @4
    c.x
    cU
    cF
    cV
    @36
    @42
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e2
    imasring.u
    imasring.v
    imasring.r
    imasring.t
    @13
    imasmulval
    3adant3r2
    #
    oveq12d
    3eqtr4d
    @45
    @115
    @109
    @117
    @111
    @45
    @37
    @8
    @114
    @108
    @4
    @103
    @45
    @40
    @10
    @43
    @29
    @3
    @104
    @106
    oveq12d
    oveq12d
    @45
    @71
    @12
    @116
    @110
    @3
    @105
    @45
    @37
    @8
    @43
    @29
    @4
    @103
    @106
    oveq12d
    #
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
    @31
    @8
    @10
    @3
    co
    #
    @29
    @4
    co
    #
    @110
    @33
    @3
    co
    #
    wceq
    #
    wph
    @31
    @47
    @139
    @63
    wph
    @46
    @139
    vx
    vy
    cV
    cV
    @66
    @45
    @139
    vz
    cV
    wph
    @64
    @65
    @67
    @45
    @139
    wi
    #
    wi
    wph
    @64
    @65
    @67
    @140
    @70
    @37
    @40
    @3
    co
    #
    @43
    @4
    co
    #
    @116
    @73
    @3
    co
    #
    wceq
    @45
    @139
    @70
    @36
    @39
    c.pl
    co
    #
    cF
    cfv
    #
    @43
    @4
    co
    #
    @122
    @79
    @3
    co
    #
    @142
    @143
    @70
    @144
    @42
    c.x
    co
    #
    cF
    cfv
    #
    @121
    @78
    c.pl
    co
    #
    cF
    cfv
    #
    @146
    @147
    @70
    @148
    @150
    cF
    @70
    @7
    @85
    @86
    @87
    @148
    @150
    wceq
    @88
    @91
    @92
    @94
    @19
    c.pl
    cR
    c.x
    @36
    @39
    @42
    @27
    imasring.p
    imasring.t
    ringdir
    syl13anc
    fveq2d
    @70
    wph
    @144
    cV
    wcel
    #
    @67
    @146
    @149
    wceq
    @96
    wph
    @64
    @65
    @152
    @67
    wph
    vu
    vv
    @36
    @39
    cV
    cV
    cV
    c.pl
    @130
    caovclg
    3adantr3
    @93
    wph
    cB
    cR
    @4
    c.x
    cU
    cF
    cV
    @144
    @42
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e2
    imasring.u
    imasring.v
    imasring.r
    imasring.t
    @13
    imasmulval
    syl3anc
    @70
    wph
    @131
    @98
    @147
    @151
    wceq
    @96
    @132
    @100
    wph
    cB
    cR
    @3
    c.pl
    cU
    cF
    cV
    @121
    @78
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e1
    imasring.u
    imasring.v
    imasring.r
    imasring.p
    @133
    imasaddval
    syl3anc
    3eqtr4d
    @70
    @141
    @145
    @43
    @4
    wph
    @64
    @65
    @141
    @145
    wceq
    @67
    wph
    cB
    cR
    @3
    c.pl
    cU
    cF
    cV
    @36
    @39
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e1
    imasring.u
    imasring.v
    imasring.r
    imasring.p
    @133
    imasaddval
    3adant3r3
    oveq1d
    @70
    @116
    @122
    @73
    @79
    @3
    @134
    @102
    oveq12d
    3eqtr4d
    @45
    @142
    @137
    @143
    @138
    @45
    @141
    @136
    @43
    @29
    @4
    @45
    @37
    @8
    @40
    @10
    @3
    @103
    @104
    oveq12d
    @106
    oveq12d
    @45
    @116
    @110
    @73
    @33
    @3
    @135
    @107
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
    c.1
    cF
    wph
    @57
    cV
    cB
    cF
    wf
    imasring.f
    cV
    cB
    cF
    fof
    syl
    wph
    c.1
    @19
    cV
    wph
    @7
    c.1
    @19
    wcel
    imasring.r
    @19
    cR
    c.1
    @27
    imasring.o
    ringidcl
    syl
    imasring.v
    eleqtrrd
    #
    ffvelrnd
    #
    wph
    @9
    @1
    @8
    @4
    co
    #
    @8
    wceq
    #
    wph
    @9
    @48
    @156
    wph
    @53
    @9
    @48
    @59
    wph
    @60
    @53
    @48
    wb
    @61
    @62
    syl
    bitr3d
    #
    wph
    @38
    @156
    vx
    cV
    wph
    @64
    wa
    #
    @1
    @37
    @4
    co
    #
    @37
    wceq
    @38
    @156
    @158
    @159
    c.1
    @36
    c.x
    co
    #
    cF
    cfv
    #
    @37
    @158
    wph
    c.1
    cV
    wcel
    #
    @64
    @159
    @161
    wceq
    wph
    @64
    simpl
    wph
    @162
    @64
    @153
    adantr
    #
    wph
    @64
    simpr
    wph
    cB
    cR
    @4
    c.x
    cU
    cF
    cV
    c.1
    @36
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e2
    imasring.u
    imasring.v
    imasring.r
    imasring.t
    @13
    imasmulval
    syl3anc
    @158
    @160
    @36
    cF
    @158
    @7
    @85
    @160
    @36
    wceq
    wph
    @7
    @64
    imasring.r
    adantr
    #
    wph
    @64
    @85
    wph
    cV
    @19
    @36
    imasring.v
    eleq2d
    biimpa
    #
    @19
    cR
    c.x
    c.1
    @36
    @27
    imasring.t
    imasring.o
    ringlidm
    syl2anc
    fveq2d
    eqtrd
    @38
    @159
    @155
    @37
    @8
    @37
    @8
    @1
    @4
    oveq2
    @38
    id
    #
    eqeq12d
    syl5ibcom
    rexlimdva
    sylbid
    #
    imp
    wph
    @9
    @8
    @1
    @4
    co
    #
    @8
    wceq
    #
    wph
    @9
    @48
    @169
    @157
    wph
    @38
    @169
    vx
    cV
    @158
    @37
    @1
    @4
    co
    #
    @37
    wceq
    @38
    @169
    @158
    @170
    @36
    c.1
    c.x
    co
    #
    cF
    cfv
    #
    @37
    wph
    @64
    @162
    @170
    @172
    wceq
    @163
    wph
    cB
    cR
    @4
    c.x
    cU
    cF
    cV
    @36
    c.1
    crg
    vq
    vp
    va
    vb
    imasring.f
    imasring.e2
    imasring.u
    imasring.v
    imasring.r
    imasring.t
    @13
    imasmulval
    mpd3an3
    @158
    @171
    @36
    cF
    @158
    @7
    @85
    @171
    @36
    wceq
    @164
    @165
    @19
    cR
    c.x
    c.1
    @36
    @27
    imasring.t
    imasring.o
    ringridm
    syl2anc
    fveq2d
    eqtrd
    @38
    @170
    @168
    @37
    @8
    @37
    @8
    @1
    @4
    oveq1
    @166
    eqeq12d
    syl5ibcom
    rexlimdva
    sylbid
    #
    imp
    isringd
    #
    wph
    @2
    @1
    wph
    @1
    cU
    cbs
    cfv
    #
    wcel
    #
    @156
    @169
    wa
    #
    vu
    @175
    wral
    #
    @2
    @1
    wceq
    #
    wph
    @1
    cB
    @175
    @154
    @5
    eleqtrd
    wph
    @177
    vu
    @175
    wph
    @8
    @175
    wcel
    @9
    @177
    wph
    cB
    @175
    @8
    @5
    eleq2d
    wph
    @9
    @156
    @169
    @167
    @173
    jcad
    sylbird
    ralrimiv
    wph
    @0
    @176
    @178
    wa
    @179
    wb
    @174
    vu
    @175
    cU
    @4
    @2
    @1
    @175
    eqid
    @13
    @2
    eqid
    isringid
    syl
    mpbi2and
    eqcomd
    jca
end
