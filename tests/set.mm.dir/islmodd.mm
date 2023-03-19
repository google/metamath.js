include "cgrp.mm"
include "wcel.mm"
include "csca.mm"
include "cfv.mm"
include "crg.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cbs.mm"
include "cplusg.mm"
include "wceq.mm"
include "w3a.mm"
include "cmulr.mm"
include "cur.mm"
include "wa.mm"
include "wral.mm"
include "clmod.mm"
include "eqeltrrd.mm"
include "3expb.mm"
include "ralrimivva.mm"
include "wi.mm"
include "weq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "ad2ant2l.mm"
include "mpan9.mm"
include "ralrimivvva.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "rspc3v.mm"
include "3com23.mm"
include "adantll.mm"
include "simpll.mm"
include "3exp2.mm"
include "imp43.mm"
include "sylan2.mm"
include "simprlr.mm"
include "simprrr.mm"
include "syl2anc.mm"
include "mpd.mm"
include "3jca.mm"
include "ralrimiva.mm"
include "id.mm"
include "rspcv.mm"
include "ad2antll.mm"
include "jca32.mm"
include "anassrs.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "oveqd.mm"
include "eleq12d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "3anbi123d.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "mpbid.mm"
include "eqid.mm"
include "islmod.mm"
include "syl3anbrc.mm"

theorem islmodd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let c.pd: class .+^
  let c.x: class .x.
  let c.xp: class .X.
  let c.1: class .1.
  let cF: class F
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vu: setvar u
  let vw: setvar w
  assume islmodd.v: |- ( ph -> V = ( Base ` W ) )
  assume islmodd.a: |- ( ph -> .+ = ( +g ` W ) )
  assume islmodd.f: |- ( ph -> F = ( Scalar ` W ) )
  assume islmodd.s: |- ( ph -> .x. = ( .s ` W ) )
  assume islmodd.b: |- ( ph -> B = ( Base ` F ) )
  assume islmodd.p: |- ( ph -> .+^ = ( +g ` F ) )
  assume islmodd.t: |- ( ph -> .X. = ( .r ` F ) )
  assume islmodd.u: |- ( ph -> .1. = ( 1r ` F ) )
  assume islmodd.r: |- ( ph -> F e. Ring )
  assume islmodd.l: |- ( ph -> W e. Grp )
  assume islmodd.w: |- ( ( ph /\ x e. B /\ y e. V ) -> ( x .x. y ) e. V )
  assume islmodd.c: |- ( ( ph /\ ( x e. B /\ y e. V /\ z e. V ) ) -> ( x .x. ( y .+ z ) ) = ( ( x .x. y ) .+ ( x .x. z ) ) )
  assume islmodd.d: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. V ) ) -> ( ( x .+^ y ) .x. z ) = ( ( x .x. z ) .+ ( y .x. z ) ) )
  assume islmodd.e: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. V ) ) -> ( ( x .X. y ) .x. z ) = ( x .x. ( y .x. z ) ) )
  assume islmodd.g: |- ( ( ph /\ x e. V ) -> ( .1. .x. x ) = x )

  disjoint y z
  disjoint .+^ y
  disjoint .+^ z
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint W x
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint .X. y
  disjoint .X. z
  disjoint .1. x
  disjoint r u
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint B r
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint ph r
  disjoint ph u
  disjoint ph w
  disjoint V u
  disjoint V w
  disjoint W r
  disjoint W u
  disjoint W w
  assert |- ( ph -> W e. LMod )

  proof
    wph
    cW
    cgrp
    wcel
    cW
    csca
    cfv
    #
    crg
    wcel
    vr
    cv
    #
    vw
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    cW
    cbs
    cfv
    #
    wcel
    #
    @1
    @2
    vu
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    @3
    co
    #
    @4
    @1
    @7
    @3
    co
    #
    @8
    co
    #
    wceq
    #
    vx
    cv
    #
    @1
    @0
    cplusg
    cfv
    #
    co
    #
    @2
    @3
    co
    #
    @14
    @2
    @3
    co
    #
    @4
    @8
    co
    #
    wceq
    #
    w3a
    #
    @14
    @1
    @0
    cmulr
    cfv
    #
    co
    #
    @2
    @3
    co
    #
    @14
    @4
    @3
    co
    #
    wceq
    #
    @0
    cur
    cfv
    #
    @2
    @3
    co
    #
    @2
    wceq
    #
    wa
    #
    wa
    #
    vw
    @5
    wral
    #
    vu
    @5
    wral
    #
    vr
    @0
    cbs
    cfv
    #
    wral
    #
    vx
    @34
    wral
    #
    cW
    clmod
    wcel
    islmodd.l
    wph
    cF
    @0
    crg
    islmodd.f
    islmodd.r
    eqeltrrd
    wph
    @1
    @2
    c.x
    co
    #
    cV
    wcel
    #
    @1
    @2
    @7
    c.pl
    co
    #
    c.x
    co
    #
    @37
    @1
    @7
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    @14
    @1
    c.pd
    co
    #
    @2
    c.x
    co
    #
    @14
    @2
    c.x
    co
    #
    @37
    c.pl
    co
    #
    wceq
    #
    w3a
    #
    @14
    @1
    c.xp
    co
    #
    @2
    c.x
    co
    #
    @14
    @37
    c.x
    co
    #
    wceq
    #
    c.1
    @2
    c.x
    co
    #
    @2
    wceq
    #
    wa
    #
    wa
    #
    vw
    cV
    wral
    #
    vu
    cV
    wral
    #
    vr
    cB
    wral
    #
    vx
    cB
    wral
    @36
    wph
    @59
    vx
    vr
    cB
    cB
    wph
    @14
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    wa
    #
    wa
    @57
    vu
    vw
    cV
    cV
    wph
    @63
    @7
    cV
    wcel
    #
    @2
    cV
    wcel
    #
    wa
    #
    @57
    wph
    @63
    @66
    wa
    #
    wa
    #
    @49
    @53
    @55
    @68
    @38
    @43
    @48
    wph
    @14
    vy
    cv
    #
    c.x
    co
    #
    cV
    wcel
    #
    vy
    cV
    wral
    vx
    cB
    wral
    #
    @67
    @38
    wph
    @71
    vx
    vy
    cB
    cV
    wph
    @61
    @69
    cV
    wcel
    @71
    islmodd.w
    3expb
    ralrimivva
    @62
    @65
    @72
    @38
    wi
    @61
    @64
    @71
    @38
    @1
    @69
    c.x
    co
    #
    cV
    wcel
    vx
    vy
    @1
    @2
    cB
    cV
    vx
    vr
    weq
    #
    @70
    @73
    cV
    @14
    @1
    @69
    c.x
    oveq1
    #
    eleq1d
    vy
    vw
    weq
    #
    @73
    @37
    cV
    @69
    @2
    @1
    c.x
    oveq2
    #
    eleq1d
    rspc2v
    ad2ant2l
    mpan9
    wph
    @14
    @69
    vz
    cv
    #
    c.pl
    co
    #
    c.x
    co
    #
    @70
    @14
    @78
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vz
    cV
    wral
    vy
    cV
    wral
    vx
    cB
    wral
    #
    @67
    @43
    wph
    @83
    vx
    vy
    vz
    cB
    cV
    cV
    islmodd.c
    ralrimivvva
    @62
    @66
    @84
    @43
    wi
    #
    @61
    @62
    @64
    @65
    @85
    @62
    @65
    @64
    @85
    @83
    @43
    @1
    @79
    c.x
    co
    #
    @73
    @1
    @78
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    @1
    @2
    @78
    c.pl
    co
    #
    c.x
    co
    #
    @37
    @87
    c.pl
    co
    #
    wceq
    vx
    vy
    vz
    @1
    @2
    @7
    cB
    cV
    cV
    @74
    @80
    @86
    @82
    @88
    @14
    @1
    @79
    c.x
    oveq1
    @74
    @70
    @73
    @81
    @87
    c.pl
    @75
    @14
    @1
    @78
    c.x
    oveq1
    oveq12d
    eqeq12d
    @76
    @86
    @90
    @88
    @91
    @76
    @79
    @89
    @1
    c.x
    @69
    @2
    @78
    c.pl
    oveq1
    oveq2d
    @76
    @73
    @37
    @87
    c.pl
    @77
    oveq1d
    eqeq12d
    vz
    vu
    weq
    #
    @90
    @40
    @91
    @42
    @92
    @89
    @39
    @1
    c.x
    @78
    @7
    @2
    c.pl
    oveq2
    oveq2d
    @92
    @87
    @41
    @37
    c.pl
    @78
    @7
    @1
    c.x
    oveq2
    oveq2d
    eqeq12d
    rspc3v
    3com23
    3expb
    adantll
    mpan9
    @68
    @14
    @69
    c.pd
    co
    #
    @78
    c.x
    co
    #
    @81
    @69
    @78
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vz
    cV
    wral
    vy
    cB
    wral
    #
    @48
    @67
    wph
    @61
    @98
    @61
    @62
    @66
    simpll
    #
    wph
    @61
    wa
    #
    @97
    vy
    vz
    cB
    cV
    wph
    @61
    @69
    cB
    wcel
    #
    @78
    cV
    wcel
    #
    @97
    wph
    @61
    @101
    @102
    @97
    islmodd.d
    3exp2
    imp43
    ralrimivva
    sylan2
    @68
    @62
    @65
    @98
    @48
    wi
    wph
    @61
    @62
    @66
    simprlr
    #
    wph
    @63
    @64
    @65
    simprrr
    #
    @97
    @48
    @44
    @78
    c.x
    co
    #
    @81
    @87
    c.pl
    co
    #
    wceq
    vy
    vz
    @1
    @2
    cB
    cV
    vy
    vr
    weq
    #
    @94
    @105
    @96
    @106
    @107
    @93
    @44
    @78
    c.x
    @69
    @1
    @14
    c.pd
    oveq2
    oveq1d
    @107
    @95
    @87
    @81
    c.pl
    @69
    @1
    @78
    c.x
    oveq1
    #
    oveq2d
    eqeq12d
    vz
    vw
    weq
    #
    @105
    @45
    @106
    @47
    @78
    @2
    @44
    c.x
    oveq2
    @109
    @81
    @46
    @87
    @37
    c.pl
    @78
    @2
    @14
    c.x
    oveq2
    @78
    @2
    @1
    c.x
    oveq2
    #
    oveq12d
    eqeq12d
    rspc2v
    syl2anc
    mpd
    3jca
    @68
    @14
    @69
    c.xp
    co
    #
    @78
    c.x
    co
    #
    @14
    @95
    c.x
    co
    #
    wceq
    #
    vz
    cV
    wral
    vy
    cB
    wral
    #
    @53
    @67
    wph
    @61
    @115
    @99
    @100
    @114
    vy
    vz
    cB
    cV
    wph
    @61
    @101
    @102
    @114
    wph
    @61
    @101
    @102
    @114
    islmodd.e
    3exp2
    imp43
    ralrimivva
    sylan2
    @68
    @62
    @65
    @115
    @53
    wi
    @103
    @104
    @114
    @53
    @50
    @78
    c.x
    co
    #
    @14
    @87
    c.x
    co
    #
    wceq
    vy
    vz
    @1
    @2
    cB
    cV
    @107
    @112
    @116
    @113
    @117
    @107
    @111
    @50
    @78
    c.x
    @69
    @1
    @14
    c.xp
    oveq2
    oveq1d
    @107
    @95
    @87
    @14
    c.x
    @108
    oveq2d
    eqeq12d
    @109
    @116
    @51
    @117
    @52
    @78
    @2
    @50
    c.x
    oveq2
    @109
    @87
    @37
    @14
    c.x
    @110
    oveq2d
    eqeq12d
    rspc2v
    syl2anc
    mpd
    wph
    c.1
    @14
    c.x
    co
    #
    @14
    wceq
    #
    vx
    cV
    wral
    #
    @67
    @55
    wph
    @119
    vx
    cV
    islmodd.g
    ralrimiva
    @65
    @120
    @55
    wi
    @63
    @64
    @119
    @55
    vx
    @2
    cV
    vx
    vw
    weq
    #
    @118
    @54
    @14
    @2
    @14
    @2
    c.1
    c.x
    oveq2
    @121
    id
    eqeq12d
    rspcv
    ad2antll
    mpan9
    jca32
    anassrs
    ralrimivva
    ralrimivva
    wph
    @60
    @35
    vx
    cB
    @34
    wph
    cB
    cF
    cbs
    cfv
    @34
    islmodd.b
    wph
    cF
    @0
    cbs
    islmodd.f
    fveq2d
    eqtrd
    #
    wph
    @59
    @33
    vr
    cB
    @34
    @122
    wph
    @58
    @32
    vu
    cV
    @5
    islmodd.v
    wph
    @57
    @31
    vw
    cV
    @5
    islmodd.v
    wph
    @49
    @21
    @56
    @30
    wph
    @38
    @6
    @43
    @13
    @48
    @20
    wph
    @37
    @4
    cV
    @5
    wph
    c.x
    @3
    @1
    @2
    islmodd.s
    oveqd
    #
    islmodd.v
    eleq12d
    wph
    @40
    @10
    @42
    @12
    wph
    @1
    @1
    @39
    @9
    c.x
    @3
    islmodd.s
    wph
    @1
    eqidd
    wph
    c.pl
    @8
    @2
    @7
    islmodd.a
    oveqd
    oveq123d
    wph
    @37
    @4
    @41
    @11
    c.pl
    @8
    islmodd.a
    @123
    wph
    c.x
    @3
    @1
    @7
    islmodd.s
    oveqd
    oveq123d
    eqeq12d
    wph
    @45
    @17
    @47
    @19
    wph
    @44
    @16
    @2
    @2
    c.x
    @3
    islmodd.s
    wph
    c.pd
    @15
    @14
    @1
    wph
    c.pd
    cF
    cplusg
    cfv
    @15
    islmodd.p
    wph
    cF
    @0
    cplusg
    islmodd.f
    fveq2d
    eqtrd
    oveqd
    wph
    @2
    eqidd
    #
    oveq123d
    wph
    @46
    @18
    @37
    @4
    c.pl
    @8
    islmodd.a
    wph
    c.x
    @3
    @14
    @2
    islmodd.s
    oveqd
    @123
    oveq123d
    eqeq12d
    3anbi123d
    wph
    @53
    @26
    @55
    @29
    wph
    @51
    @24
    @52
    @25
    wph
    @50
    @23
    @2
    @2
    c.x
    @3
    islmodd.s
    wph
    c.xp
    @22
    @14
    @1
    wph
    c.xp
    cF
    cmulr
    cfv
    @22
    islmodd.t
    wph
    cF
    @0
    cmulr
    islmodd.f
    fveq2d
    eqtrd
    oveqd
    @124
    oveq123d
    wph
    @14
    @14
    @37
    @4
    c.x
    @3
    islmodd.s
    wph
    @14
    eqidd
    @123
    oveq123d
    eqeq12d
    wph
    @54
    @28
    @2
    wph
    c.1
    @27
    @2
    @2
    c.x
    @3
    islmodd.s
    wph
    c.1
    cF
    cur
    cfv
    @27
    islmodd.u
    wph
    cF
    @0
    cur
    islmodd.f
    fveq2d
    eqtrd
    @124
    oveq123d
    eqeq1d
    anbi12d
    anbi12d
    raleqbidv
    raleqbidv
    raleqbidv
    raleqbidv
    mpbid
    vu
    vw
    @8
    @15
    @3
    @22
    @27
    @0
    @34
    @5
    cW
    vr
    vx
    @5
    eqid
    @8
    eqid
    @3
    eqid
    @0
    eqid
    @34
    eqid
    @15
    eqid
    @22
    eqid
    @27
    eqid
    islmod
    syl3anbrc
end
