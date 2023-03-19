include "clmod.mm"
include "wcel.mm"
include "cgrp.mm"
include "crg.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "wa.mm"
include "wral.mm"
include "cur.mm"
include "cfv.mm"
include "cmulr.mm"
include "wsbc.mm"
include "cplusg.mm"
include "cbs.mm"
include "cvsca.mm"
include "csca.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "sbceq1d.mm"
include "sbceqbid.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "simp3.mm"
include "fveq2d.mm"
include "oveq.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "anbi1d.mm"
include "anbi2d.mm"
include "2ralbidv.mm"
include "sbcie.mm"
include "eleq1d.mm"
include "simp1.mm"
include "eleq2d.mm"
include "simp2.mm"
include "oveqd.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "eqeq2d.mm"
include "3anbi123d.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "sbcbidv.mm"
include "sbc3ie.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "bitri.mm"
include "syl6bb.mm"
include "df-lmod.mm"
include "elrab2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem islmod
  let vx: setvar x
  let vw: setvar w
  let c.pl: class .+
  let c.pd: class .+^
  let c.x: class .x.
  let c.xp: class .X.
  let c.1: class .1.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let vr: setvar r
  let vq: setvar q
  let va: setvar a
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let vp: setvar p
  let vs: setvar s
  let vv: setvar v
  let cR: class R
  let cX: class X
  let cQ: class Q
  let cY: class Y
  let vt: setvar t
  assume islmod.v: |- V = ( Base ` W )
  assume islmod.a: |- .+ = ( +g ` W )
  assume islmod.s: |- .x. = ( .s ` W )
  assume islmod.f: |- F = ( Scalar ` W )
  assume islmod.k: |- K = ( Base ` F )
  assume islmod.p: |- .+^ = ( +g ` F )
  assume islmod.t: |- .X. = ( .r ` F )
  assume islmod.u: |- .1. = ( 1r ` F )

  disjoint q r
  disjoint q w
  disjoint q x
  disjoint F q
  disjoint r w
  disjoint r x
  disjoint F r
  disjoint w x
  disjoint F w
  disjoint F x
  disjoint K q
  disjoint K r
  disjoint K w
  disjoint K x
  disjoint .+^ q
  disjoint .+^ r
  disjoint .+^ w
  disjoint .+^ x
  disjoint V q
  disjoint V r
  disjoint V w
  disjoint V x
  disjoint .+ q
  disjoint .+ r
  disjoint .+ w
  disjoint .+ x
  disjoint .1. q
  disjoint .1. r
  disjoint .1. w
  disjoint .1. x
  disjoint .X. q
  disjoint .X. r
  disjoint .X. w
  disjoint .X. x
  disjoint .x. q
  disjoint .x. r
  disjoint .x. w
  disjoint .x. x
  disjoint a f
  disjoint a g
  disjoint a k
  disjoint a p
  disjoint a q
  disjoint a r
  disjoint a s
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint F a
  disjoint f g
  disjoint f k
  disjoint f p
  disjoint f q
  disjoint f r
  disjoint f s
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint F f
  disjoint g k
  disjoint g p
  disjoint g q
  disjoint g r
  disjoint g s
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint F g
  disjoint k p
  disjoint k q
  disjoint k r
  disjoint k s
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint F k
  disjoint p q
  disjoint p r
  disjoint p s
  disjoint p v
  disjoint p w
  disjoint p x
  disjoint F p
  disjoint q s
  disjoint q v
  disjoint r s
  disjoint r v
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint F s
  disjoint v w
  disjoint v x
  disjoint F v
  disjoint K a
  disjoint K f
  disjoint K g
  disjoint K k
  disjoint K p
  disjoint K s
  disjoint K v
  disjoint R r
  disjoint R w
  disjoint R x
  disjoint .+^ a
  disjoint .+^ f
  disjoint .+^ g
  disjoint .+^ k
  disjoint .+^ p
  disjoint .+^ s
  disjoint .+^ v
  disjoint V a
  disjoint V f
  disjoint V g
  disjoint V k
  disjoint V p
  disjoint V s
  disjoint V v
  disjoint X w
  disjoint X x
  disjoint .+ a
  disjoint .+ f
  disjoint .+ g
  disjoint .+ k
  disjoint .+ p
  disjoint .+ s
  disjoint .+ v
  disjoint Q q
  disjoint Q r
  disjoint Q w
  disjoint Q x
  disjoint W a
  disjoint W f
  disjoint W g
  disjoint W v
  disjoint Y w
  disjoint .1. a
  disjoint .1. f
  disjoint .1. g
  disjoint .1. k
  disjoint .1. p
  disjoint .1. s
  disjoint .1. v
  disjoint a t
  disjoint .X. a
  disjoint f t
  disjoint .X. f
  disjoint g t
  disjoint .X. g
  disjoint k t
  disjoint .X. k
  disjoint p t
  disjoint .X. p
  disjoint q t
  disjoint r t
  disjoint s t
  disjoint .X. s
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint .X. t
  disjoint .X. v
  disjoint .x. a
  disjoint .x. f
  disjoint .x. g
  disjoint .x. k
  disjoint .x. p
  disjoint .x. s
  disjoint .x. v
  assert |- ( W e. LMod <-> ( W e. Grp /\ F e. Ring /\ A. q e. K A. r e. K A. x e. V A. w e. V ( ( ( r .x. w ) e. V /\ ( r .x. ( w .+ x ) ) = ( ( r .x. w ) .+ ( r .x. x ) ) /\ ( ( q .+^ r ) .x. w ) = ( ( q .x. w ) .+ ( r .x. w ) ) ) /\ ( ( ( q .X. r ) .x. w ) = ( q .x. ( r .x. w ) ) /\ ( .1. .x. w ) = w ) ) ) )

  proof
    cW
    clmod
    wcel
    cW
    cgrp
    wcel
    #
    cF
    crg
    wcel
    #
    vr
    cv
    #
    vw
    cv
    #
    c.x
    co
    #
    cV
    wcel
    #
    @2
    @3
    vx
    cv
    #
    c.pl
    co
    #
    c.x
    co
    #
    @4
    @2
    @6
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    vq
    cv
    #
    @2
    c.pd
    co
    #
    @3
    c.x
    co
    #
    @12
    @3
    c.x
    co
    #
    @4
    c.pl
    co
    #
    wceq
    #
    w3a
    #
    @12
    @2
    c.xp
    co
    #
    @3
    c.x
    co
    #
    @12
    @4
    c.x
    co
    #
    wceq
    #
    c.1
    @3
    c.x
    co
    #
    @3
    wceq
    #
    wa
    #
    wa
    #
    vw
    cV
    wral
    vx
    cV
    wral
    #
    vr
    cK
    wral
    #
    vq
    cK
    wral
    #
    wa
    #
    wa
    @0
    @1
    @29
    w3a
    vf
    cv
    #
    crg
    wcel
    #
    @2
    @3
    vs
    cv
    #
    co
    #
    vv
    cv
    #
    wcel
    #
    @2
    @3
    @6
    va
    cv
    #
    co
    #
    @33
    co
    #
    @34
    @2
    @6
    @33
    co
    #
    @37
    co
    #
    wceq
    #
    @12
    @2
    vp
    cv
    #
    co
    #
    @3
    @33
    co
    #
    @12
    @3
    @33
    co
    #
    @34
    @37
    co
    #
    wceq
    #
    w3a
    #
    @12
    @2
    vt
    cv
    #
    co
    #
    @3
    @33
    co
    #
    @12
    @34
    @33
    co
    #
    wceq
    #
    @31
    cur
    cfv
    #
    @3
    @33
    co
    #
    @3
    wceq
    #
    wa
    #
    wa
    #
    vw
    @35
    wral
    vx
    @35
    wral
    #
    vr
    vk
    cv
    #
    wral
    vq
    @61
    wral
    #
    wa
    #
    vt
    @31
    cmulr
    cfv
    #
    wsbc
    #
    vp
    @31
    cplusg
    cfv
    #
    wsbc
    #
    vk
    @31
    cbs
    cfv
    #
    wsbc
    #
    vs
    vg
    cv
    #
    cvsca
    cfv
    #
    wsbc
    #
    vf
    @70
    csca
    cfv
    #
    wsbc
    #
    va
    @70
    cplusg
    cfv
    #
    wsbc
    #
    vv
    @70
    cbs
    cfv
    #
    wsbc
    #
    @30
    vg
    cW
    cgrp
    clmod
    @70
    cW
    wceq
    #
    @78
    @69
    vs
    c.x
    wsbc
    #
    vf
    cF
    wsbc
    #
    va
    c.pl
    wsbc
    #
    vv
    cV
    wsbc
    #
    @30
    @79
    @76
    @82
    vv
    @77
    cV
    @79
    @77
    cW
    cbs
    cfv
    #
    cV
    @70
    cW
    cbs
    fveq2
    islmod.v
    syl6eqr
    @79
    @74
    @81
    va
    @75
    c.pl
    @79
    @75
    cW
    cplusg
    cfv
    #
    c.pl
    @70
    cW
    cplusg
    fveq2
    islmod.a
    syl6eqr
    @79
    @72
    @80
    vf
    @73
    cF
    @79
    @73
    cW
    csca
    cfv
    #
    cF
    @70
    cW
    csca
    fveq2
    islmod.f
    syl6eqr
    @79
    @69
    vs
    @71
    c.x
    @79
    @71
    cW
    cvsca
    cfv
    #
    c.x
    @70
    cW
    cvsca
    fveq2
    islmod.s
    syl6eqr
    sbceq1d
    sbceqbid
    sbceqbid
    sbceqbid
    @83
    @1
    @34
    cV
    wcel
    #
    @2
    @7
    @33
    co
    #
    @34
    @40
    c.pl
    co
    #
    wceq
    #
    @45
    @46
    @34
    c.pl
    co
    #
    wceq
    #
    w3a
    #
    @19
    @3
    @33
    co
    #
    @53
    wceq
    #
    c.1
    @3
    @33
    co
    #
    @3
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
    vx
    cV
    wral
    #
    vr
    @61
    wral
    #
    vq
    @61
    wral
    #
    wa
    #
    vp
    c.pd
    wsbc
    #
    vk
    cK
    wsbc
    #
    vs
    c.x
    wsbc
    #
    @30
    @80
    @108
    vv
    va
    vf
    cV
    c.pl
    cF
    cV
    @84
    cvv
    islmod.v
    cW
    cbs
    fvex
    eqeltri
    c.pl
    @85
    cvv
    islmod.a
    cW
    cplusg
    fvex
    eqeltri
    cF
    @86
    cvv
    islmod.f
    cW
    csca
    fvex
    eqeltri
    @35
    cV
    wceq
    #
    @37
    c.pl
    wceq
    #
    @31
    cF
    wceq
    #
    w3a
    #
    @69
    @107
    vs
    c.x
    @112
    @67
    @106
    vk
    @68
    cK
    @112
    @68
    cF
    cbs
    cfv
    #
    cK
    @112
    @31
    cF
    cbs
    @109
    @110
    @111
    simp3
    #
    fveq2d
    islmod.k
    syl6eqr
    @112
    @65
    @105
    vp
    @66
    c.pd
    @112
    @66
    cF
    cplusg
    cfv
    #
    c.pd
    @112
    @31
    cF
    cplusg
    @114
    fveq2d
    islmod.p
    syl6eqr
    @112
    @65
    @63
    vt
    c.xp
    wsbc
    #
    @105
    @112
    @63
    vt
    @64
    c.xp
    @112
    @64
    cF
    cmulr
    cfv
    #
    c.xp
    @112
    @31
    cF
    cmulr
    @114
    fveq2d
    islmod.t
    syl6eqr
    sbceq1d
    @116
    @32
    @49
    @96
    @57
    wa
    #
    wa
    #
    vw
    @35
    wral
    #
    vx
    @35
    wral
    #
    vr
    @61
    wral
    vq
    @61
    wral
    #
    wa
    #
    @112
    @105
    @63
    @123
    vt
    c.xp
    c.xp
    @117
    cvv
    islmod.t
    cF
    cmulr
    fvex
    eqeltri
    @50
    c.xp
    wceq
    #
    @62
    @122
    @32
    @124
    @60
    @121
    vq
    vr
    @61
    @61
    @124
    @59
    @119
    vx
    vw
    @35
    @35
    @124
    @58
    @118
    @49
    @124
    @54
    @96
    @57
    @124
    @52
    @95
    @53
    @124
    @51
    @19
    @3
    @33
    @12
    @2
    @50
    c.xp
    oveq
    oveq1d
    eqeq1d
    anbi1d
    anbi2d
    2ralbidv
    2ralbidv
    anbi2d
    sbcie
    @112
    @32
    @1
    @122
    @104
    @112
    @31
    cF
    crg
    @114
    eleq1d
    @112
    @121
    @102
    vq
    vr
    @61
    @61
    @112
    @120
    @101
    vx
    @35
    cV
    @109
    @110
    @111
    simp1
    #
    @112
    @119
    @100
    vw
    @35
    cV
    @125
    @112
    @49
    @94
    @118
    @99
    @112
    @36
    @88
    @42
    @91
    @48
    @93
    @112
    @35
    cV
    @34
    @125
    eleq2d
    @112
    @39
    @89
    @41
    @90
    @112
    @38
    @7
    @2
    @33
    @112
    @37
    c.pl
    @3
    @6
    @109
    @110
    @111
    simp2
    #
    oveqd
    oveq2d
    @112
    @37
    c.pl
    @34
    @40
    @126
    oveqd
    eqeq12d
    @112
    @47
    @92
    @45
    @112
    @37
    c.pl
    @46
    @34
    @126
    oveqd
    eqeq2d
    3anbi123d
    @112
    @57
    @98
    @96
    @112
    @56
    @97
    @3
    @112
    @55
    c.1
    @3
    @33
    @112
    @55
    cF
    cur
    cfv
    c.1
    @112
    @31
    cF
    cur
    @114
    fveq2d
    islmod.u
    syl6eqr
    oveq1d
    eqeq1d
    anbi2d
    anbi12d
    raleqbidv
    raleqbidv
    2ralbidv
    anbi12d
    syl5bb
    bitrd
    sbceqbid
    sbceqbid
    sbcbidv
    sbc3ie
    @105
    @30
    vs
    vk
    vp
    c.x
    cK
    c.pd
    c.x
    @87
    cvv
    islmod.s
    cW
    cvsca
    fvex
    eqeltri
    cK
    @113
    cvv
    islmod.k
    cF
    cbs
    fvex
    eqeltri
    c.pd
    @115
    cvv
    islmod.p
    cF
    cplusg
    fvex
    eqeltri
    @33
    c.x
    wceq
    #
    @61
    cK
    wceq
    #
    @43
    c.pd
    wceq
    #
    w3a
    #
    @104
    @29
    @1
    @130
    @103
    @28
    vq
    @61
    cK
    @127
    @128
    @129
    simp2
    #
    @130
    @102
    @27
    vr
    @61
    cK
    @131
    @130
    @100
    @26
    vx
    vw
    cV
    cV
    @130
    @94
    @18
    @99
    @25
    @130
    @88
    @5
    @91
    @11
    @93
    @17
    @130
    @34
    @4
    cV
    @130
    @33
    c.x
    @2
    @3
    @127
    @128
    @129
    simp1
    #
    oveqd
    #
    eleq1d
    @130
    @89
    @8
    @90
    @10
    @130
    @33
    c.x
    @2
    @7
    @132
    oveqd
    @130
    @34
    @4
    @40
    @9
    c.pl
    @133
    @130
    @33
    c.x
    @2
    @6
    @132
    oveqd
    oveq12d
    eqeq12d
    @130
    @45
    @14
    @92
    @16
    @130
    @45
    @13
    @3
    @33
    co
    @14
    @130
    @44
    @13
    @3
    @33
    @130
    @43
    c.pd
    @12
    @2
    @127
    @128
    @129
    simp3
    oveqd
    oveq1d
    @130
    @33
    c.x
    @13
    @3
    @132
    oveqd
    eqtrd
    @130
    @46
    @15
    @34
    @4
    c.pl
    @130
    @33
    c.x
    @12
    @3
    @132
    oveqd
    @133
    oveq12d
    eqeq12d
    3anbi123d
    @130
    @96
    @22
    @98
    @24
    @130
    @95
    @20
    @53
    @21
    @130
    @33
    c.x
    @19
    @3
    @132
    oveqd
    @130
    @53
    @12
    @4
    @33
    co
    @21
    @130
    @34
    @4
    @12
    @33
    @133
    oveq2d
    @130
    @33
    c.x
    @12
    @4
    @132
    oveqd
    eqtrd
    eqeq12d
    @130
    @97
    @23
    @3
    @130
    @33
    c.x
    c.1
    @3
    @132
    oveqd
    eqeq1d
    anbi12d
    anbi12d
    2ralbidv
    raleqbidv
    raleqbidv
    anbi2d
    sbc3ie
    bitri
    syl6bb
    vx
    vw
    vv
    vt
    vf
    vg
    vk
    vs
    vr
    vq
    vp
    va
    df-lmod
    elrab2
    @0
    @1
    @29
    3anass
    bitr4i
end
