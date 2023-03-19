include "ccrg.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cnx.mm"
include "cvsca.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "baseid.mm"
include "c1.mm"
include "df-base.mm"
include "1nn.mm"
include "ndxarg.mm"
include "c6.mm"
include "1re.mm"
include "1lt6.mm"
include "ltneii.mm"
include "vscandx.mm"
include "neeqtrri.mm"
include "eqnetri.mm"
include "setsnid.mm"
include "eqtri.mm"
include "eqcomi.mm"
include "fveq2i.mm"
include "a1i.mm"
include "cplusg.mm"
include "plusgid.mm"
include "c2.mm"
include "plusgndx.mm"
include "2re.mm"
include "2lt6.mm"
include "3eqtr4i.mm"
include "csca.mm"
include "scaid.mm"
include "c5.mm"
include "scandx.mm"
include "5re.mm"
include "5lt6.mm"
include "cgrp.mm"
include "cvv.mm"
include "crg.mm"
include "cv.mm"
include "w3a.mm"
include "wa.mm"
include "wral.mm"
include "simp1i.mm"
include "fvexi.mm"
include "mpt2exg.mm"
include "mp2an.mm"
include "vscaid.mm"
include "setsid.mm"
include "cmulr.mm"
include "cur.mm"
include "crngring.mm"
include "eqtr4i.mm"
include "grpprop.mm"
include "mpbi.mm"
include "cmpt2.mm"
include "weq.mm"
include "oveq12.mm"
include "ancoms.mm"
include "adantl.mm"
include "simp2.mm"
include "simp3.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "wi.mm"
include "simpl1.mm"
include "2ralimi.mm"
include "c0.mm"
include "wne.mm"
include "ringgrp.mm"
include "grpbn0.mm"
include "syl.mm"
include "3ad2ant2.mm"
include "ax-mp.mm"
include "rspn0.mm"
include "ralcom.mm"
include "3ad2ant1.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "oveq1.mm"
include "rspc2v.mm"
include "3adant1.mm"
include "syl5com.mm"
include "sylbi.mm"
include "3syl.mm"
include "3ad2ant3.mm"
include "eqeltrd.mm"
include "simp1.mm"
include "grpcl.mm"
include "mp3an1.mm"
include "simpl2.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "rspc3v.mm"
include "3com23.mm"
include "eqtrd.mm"
include "eqtr4d.mm"
include "simpl3.mm"
include "ralrot3.mm"
include "3expib.mm"
include "3adant3.mm"
include "3eqtr4d.mm"
include "rmodislmodlem.mm"
include "ringidcl.mm"
include "adantr.mm"
include "simpr.mm"
include "simprr.mm"
include "id.mm"
include "rspcv.mm"
include "islmodd.mm"

theorem rmodislmod
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let c.pl: class .+
  let c.pd: class .+^
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let c.1: class .1.
  let cF: class F
  let c.as: class .*
  let cK: class K
  let cL: class L
  let cV: class V
  let vs: setvar s
  let vr: setvar r
  let vq: setvar q
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  assume rmodislmod.v: |- V = ( Base ` R )
  assume rmodislmod.a: |- .+ = ( +g ` R )
  assume rmodislmod.s: |- .x. = ( .s ` R )
  assume rmodislmod.f: |- F = ( Scalar ` R )
  assume rmodislmod.k: |- K = ( Base ` F )
  assume rmodislmod.p: |- .+^ = ( +g ` F )
  assume rmodislmod.t: |- .X. = ( .r ` F )
  assume rmodislmod.u: |- .1. = ( 1r ` F )
  assume rmodislmod.r: |- ( R e. Grp /\ F e. Ring /\ A. q e. K A. r e. K A. x e. V A. w e. V ( ( ( w .x. r ) e. V /\ ( ( w .+ x ) .x. r ) = ( ( w .x. r ) .+ ( x .x. r ) ) /\ ( w .x. ( q .+^ r ) ) = ( ( w .x. q ) .+ ( w .x. r ) ) ) /\ ( ( w .x. ( q .X. r ) ) = ( ( w .x. q ) .x. r ) /\ ( w .x. .1. ) = w ) ) )
  assume rmodislmod.m: |- .* = ( s e. K , v e. V |-> ( v .x. s ) )
  assume rmodislmod.l: |- L = ( R sSet <. ( .s ` ndx ) , .* >. )

  disjoint .X. q
  disjoint .X. r
  disjoint .X. w
  disjoint .X. x
  disjoint q r
  disjoint q w
  disjoint q x
  disjoint r w
  disjoint r x
  disjoint w x
  disjoint .X. s
  disjoint .X. v
  disjoint s v
  disjoint .x. q
  disjoint .x. r
  disjoint .x. w
  disjoint .x. x
  disjoint .x. s
  disjoint .x. v
  disjoint K q
  disjoint K r
  disjoint K x
  disjoint K s
  disjoint K v
  disjoint V q
  disjoint V r
  disjoint V w
  disjoint V x
  disjoint V s
  disjoint V v
  disjoint F s
  disjoint F v
  disjoint .1. s
  disjoint .1. v
  disjoint .1. q
  disjoint .1. r
  disjoint .1. w
  disjoint .1. x
  disjoint .+ q
  disjoint .+ r
  disjoint .+ w
  disjoint .+ x
  disjoint .+ s
  disjoint .+ v
  disjoint .+^ q
  disjoint .+^ r
  disjoint .+^ w
  disjoint .+^ x
  disjoint .+^ s
  disjoint .+^ v
  disjoint a r
  disjoint a w
  disjoint a s
  disjoint a v
  disjoint b q
  disjoint b r
  disjoint b w
  disjoint b s
  disjoint b v
  disjoint c s
  disjoint c v
  disjoint c w
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint L a
  disjoint V a
  disjoint V b
  disjoint V c
  disjoint .1. a
  disjoint .X. b
  disjoint .X. c
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  disjoint .+^ b
  disjoint .+^ c
  disjoint .* a
  disjoint .* b
  disjoint .* c
  disjoint a q
  disjoint a x
  disjoint c x
  assert |- ( F e. CRing -> L e. LMod )

  proof
    cF
    ccrg
    wcel
    #
    va
    vb
    vc
    cK
    c.pl
    c.pd
    c.as
    c.xp
    c.1
    cF
    cV
    cL
    cV
    cL
    cbs
    cfv
    #
    wceq
    @0
    cV
    cR
    cnx
    cvsca
    cfv
    #
    c.as
    cop
    csts
    co
    #
    cbs
    cfv
    #
    @1
    cV
    cR
    cbs
    cfv
    #
    @4
    rmodislmod.v
    c.as
    @2
    cbs
    cR
    baseid
    cnx
    cbs
    cfv
    c1
    @2
    cbs
    c1
    df-base
    1nn
    ndxarg
    c1
    c6
    @2
    c1
    c6
    1re
    1lt6
    ltneii
    vscandx
    neeqtrri
    eqnetri
    setsnid
    eqtri
    @3
    cL
    cbs
    cL
    @3
    rmodislmod.l
    eqcomi
    #
    fveq2i
    eqtri
    #
    a1i
    c.pl
    cL
    cplusg
    cfv
    #
    wceq
    @0
    cR
    cplusg
    cfv
    #
    @3
    cplusg
    cfv
    #
    c.pl
    @8
    c.as
    @2
    cplusg
    cR
    plusgid
    cnx
    cplusg
    cfv
    c2
    @2
    plusgndx
    c2
    c6
    @2
    c2
    c6
    2re
    2lt6
    ltneii
    vscandx
    neeqtrri
    eqnetri
    setsnid
    #
    rmodislmod.a
    cL
    @3
    cplusg
    rmodislmod.l
    fveq2i
    #
    3eqtr4i
    a1i
    cF
    cL
    csca
    cfv
    #
    wceq
    @0
    cR
    csca
    cfv
    @3
    csca
    cfv
    cF
    @13
    c.as
    @2
    csca
    cR
    scaid
    cnx
    csca
    cfv
    c5
    @2
    scandx
    c5
    c6
    @2
    c5
    c6
    5re
    5lt6
    ltneii
    vscandx
    neeqtrri
    eqnetri
    setsnid
    rmodislmod.f
    cL
    @3
    csca
    rmodislmod.l
    fveq2i
    3eqtr4i
    a1i
    c.as
    cL
    cvsca
    cfv
    #
    wceq
    @0
    c.as
    @3
    cvsca
    cfv
    #
    @14
    cR
    cgrp
    wcel
    #
    c.as
    cvv
    wcel
    #
    c.as
    @15
    wceq
    @16
    cF
    crg
    wcel
    #
    vw
    cv
    #
    vr
    cv
    #
    c.x
    co
    #
    cV
    wcel
    #
    @19
    vx
    cv
    #
    c.pl
    co
    #
    @20
    c.x
    co
    #
    @21
    @23
    @20
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    #
    @19
    vq
    cv
    #
    @20
    c.pd
    co
    #
    c.x
    co
    #
    @19
    @29
    c.x
    co
    #
    @21
    c.pl
    co
    #
    wceq
    #
    w3a
    #
    @19
    @29
    @20
    c.xp
    co
    c.x
    co
    @32
    @20
    c.x
    co
    wceq
    #
    @19
    c.1
    c.x
    co
    #
    @19
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
    vq
    cK
    wral
    #
    rmodislmod.r
    simp1i
    #
    cK
    cvv
    wcel
    cV
    cvv
    wcel
    @17
    cK
    cF
    cbs
    rmodislmod.k
    fvexi
    cV
    cR
    cbs
    rmodislmod.v
    fvexi
    vs
    vv
    cK
    cV
    vv
    cv
    #
    vs
    cv
    #
    c.x
    co
    #
    cvv
    cvv
    c.as
    rmodislmod.m
    mpt2exg
    mp2an
    cgrp
    c.as
    cvsca
    cvv
    cR
    vscaid
    setsid
    mp2an
    @3
    cL
    cvsca
    @6
    fveq2i
    eqtri
    a1i
    cK
    cF
    cbs
    cfv
    wceq
    @0
    rmodislmod.k
    a1i
    c.pd
    cF
    cplusg
    cfv
    wceq
    @0
    rmodislmod.p
    a1i
    c.xp
    cF
    cmulr
    cfv
    wceq
    @0
    rmodislmod.t
    a1i
    c.1
    cF
    cur
    cfv
    wceq
    @0
    rmodislmod.u
    a1i
    cF
    crngring
    #
    cL
    cgrp
    wcel
    #
    @0
    @16
    @48
    @43
    cR
    cL
    @5
    cV
    @1
    cV
    @5
    rmodislmod.v
    eqcomi
    @7
    eqtri
    @9
    @10
    @8
    @11
    @12
    eqtr4i
    grpprop
    mpbi
    a1i
    @0
    va
    cv
    #
    cK
    wcel
    #
    vb
    cv
    #
    cV
    wcel
    #
    w3a
    #
    @49
    @51
    c.as
    co
    #
    @51
    @49
    c.x
    co
    #
    cV
    @53
    vs
    vv
    @49
    @51
    cK
    cV
    @46
    @55
    c.as
    cvv
    c.as
    vs
    vv
    cK
    cV
    @46
    cmpt2
    wceq
    #
    @53
    rmodislmod.m
    a1i
    vs
    va
    weq
    #
    vv
    vb
    weq
    #
    wa
    #
    @46
    @55
    wceq
    #
    @53
    @58
    @57
    @60
    @44
    @51
    @45
    @49
    c.x
    oveq12
    ancoms
    #
    adantl
    @0
    @50
    @52
    simp2
    @0
    @50
    @52
    simp3
    @53
    @51
    @49
    c.x
    ovexd
    ovmpt2d
    @16
    @18
    @42
    w3a
    #
    @53
    @55
    cV
    wcel
    #
    wi
    #
    rmodislmod.r
    @42
    @16
    @64
    @18
    @42
    @22
    vw
    cV
    wral
    #
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
    @67
    @64
    @41
    @66
    vq
    vr
    cK
    cK
    @40
    @22
    vx
    vw
    cV
    cV
    @22
    @28
    @34
    @39
    simpl1
    2ralimi
    2ralimi
    cK
    c0
    wne
    #
    @68
    @67
    wi
    @62
    @69
    rmodislmod.r
    @18
    @16
    @69
    @42
    @18
    cF
    cgrp
    wcel
    #
    @69
    cF
    ringgrp
    #
    cK
    cF
    rmodislmod.k
    grpbn0
    syl
    3ad2ant2
    ax-mp
    #
    @67
    vq
    cK
    rspn0
    ax-mp
    @67
    @65
    vr
    cK
    wral
    #
    vx
    cV
    wral
    #
    @64
    @65
    vr
    vx
    cK
    cV
    ralcom
    @74
    @73
    @53
    @63
    cV
    c0
    wne
    #
    @74
    @73
    wi
    @62
    @75
    rmodislmod.r
    @16
    @18
    @75
    @42
    cV
    cR
    rmodislmod.v
    grpbn0
    3ad2ant1
    ax-mp
    #
    @73
    vx
    cV
    rspn0
    ax-mp
    @50
    @52
    @73
    @63
    wi
    @0
    @22
    @63
    @19
    @49
    c.x
    co
    #
    cV
    wcel
    vr
    vw
    @49
    @51
    cK
    cV
    vr
    va
    weq
    #
    @21
    @77
    cV
    @20
    @49
    @19
    c.x
    oveq2
    #
    eleq1d
    vw
    vb
    weq
    #
    @77
    @55
    cV
    @19
    @51
    @49
    c.x
    oveq1
    #
    eleq1d
    rspc2v
    3adant1
    syl5com
    sylbi
    3syl
    3ad2ant3
    ax-mp
    eqeltrd
    @0
    @50
    @52
    vc
    cv
    #
    cV
    wcel
    #
    w3a
    #
    wa
    @49
    @51
    @82
    c.pl
    co
    #
    c.as
    co
    #
    @55
    @82
    @49
    c.x
    co
    #
    c.pl
    co
    #
    @54
    @49
    @82
    c.as
    co
    #
    c.pl
    co
    #
    @84
    @86
    @88
    wceq
    @0
    @84
    @86
    @85
    @49
    c.x
    co
    #
    @88
    @84
    vs
    vv
    @49
    @85
    cK
    cV
    @46
    @91
    c.as
    cvv
    @56
    @84
    rmodislmod.m
    a1i
    #
    @57
    @44
    @85
    wceq
    #
    wa
    @46
    @91
    wceq
    #
    @84
    @93
    @57
    @94
    @44
    @85
    @45
    @49
    c.x
    oveq12
    ancoms
    adantl
    @50
    @52
    @83
    simp1
    #
    @52
    @83
    @85
    cV
    wcel
    #
    @50
    @16
    @52
    @83
    @96
    @43
    cV
    c.pl
    cR
    @51
    @82
    rmodislmod.v
    rmodislmod.a
    grpcl
    mp3an1
    3adant1
    @84
    @85
    @49
    c.x
    ovexd
    ovmpt2d
    @62
    @84
    @91
    @88
    wceq
    #
    wi
    #
    rmodislmod.r
    @42
    @16
    @98
    @18
    @42
    @28
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
    @98
    @41
    @99
    vq
    vr
    cK
    cK
    @40
    @28
    vx
    vw
    cV
    cV
    @22
    @28
    @34
    @39
    simpl2
    2ralimi
    2ralimi
    @101
    @100
    @84
    @97
    @69
    @101
    @100
    wi
    @72
    @100
    vq
    cK
    rspn0
    ax-mp
    @50
    @83
    @52
    @100
    @97
    wi
    @28
    @97
    @24
    @49
    c.x
    co
    #
    @77
    @23
    @49
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    @19
    @82
    c.pl
    co
    #
    @49
    c.x
    co
    #
    @77
    @87
    c.pl
    co
    #
    wceq
    vr
    vx
    vw
    @49
    @82
    @51
    cK
    cV
    cV
    @78
    @25
    @102
    @27
    @104
    @20
    @49
    @24
    c.x
    oveq2
    @78
    @21
    @77
    @26
    @103
    c.pl
    @79
    @20
    @49
    @23
    c.x
    oveq2
    oveq12d
    eqeq12d
    vx
    vc
    weq
    #
    @102
    @106
    @104
    @107
    @108
    @24
    @105
    @49
    c.x
    @23
    @82
    @19
    c.pl
    oveq2
    oveq1d
    @108
    @103
    @87
    @77
    c.pl
    @23
    @82
    @49
    c.x
    oveq1
    oveq2d
    eqeq12d
    @80
    @106
    @91
    @107
    @88
    @80
    @105
    @85
    @49
    c.x
    @19
    @51
    @82
    c.pl
    oveq1
    oveq1d
    @80
    @77
    @55
    @87
    c.pl
    @81
    oveq1d
    eqeq12d
    rspc3v
    3com23
    syl5com
    syl
    3ad2ant3
    ax-mp
    eqtrd
    adantl
    @84
    @90
    @88
    wceq
    @0
    @84
    @54
    @55
    @89
    @87
    c.pl
    @84
    vs
    vv
    @49
    @51
    cK
    cV
    @46
    @55
    c.as
    cvv
    @92
    @59
    @60
    @84
    @61
    adantl
    @95
    @50
    @52
    @83
    simp2
    @84
    @51
    @49
    c.x
    ovexd
    ovmpt2d
    @84
    vs
    vv
    @49
    @82
    cK
    cV
    @46
    @87
    c.as
    cvv
    @92
    @57
    vv
    vc
    weq
    #
    wa
    #
    @46
    @87
    wceq
    #
    @84
    @109
    @57
    @111
    @44
    @82
    @45
    @49
    c.x
    oveq12
    ancoms
    #
    adantl
    @95
    @50
    @52
    @83
    simp3
    @84
    @82
    @49
    c.x
    ovexd
    ovmpt2d
    oveq12d
    adantl
    eqtr4d
    @50
    @51
    cK
    wcel
    #
    @83
    w3a
    #
    @49
    @51
    c.pd
    co
    #
    @82
    c.as
    co
    #
    @89
    @51
    @82
    c.as
    co
    #
    c.pl
    co
    #
    wceq
    @0
    @114
    @82
    @115
    c.x
    co
    #
    @87
    @82
    @51
    c.x
    co
    #
    c.pl
    co
    #
    @116
    @118
    @62
    @114
    @119
    @121
    wceq
    #
    wi
    #
    rmodislmod.r
    @42
    @16
    @123
    @18
    @42
    @34
    vw
    cV
    wral
    #
    vx
    cV
    wral
    #
    vr
    cK
    wral
    vq
    cK
    wral
    #
    @123
    @41
    @125
    vq
    vr
    cK
    cK
    @40
    @34
    vx
    vw
    cV
    cV
    @22
    @28
    @34
    @39
    simpl3
    2ralimi
    2ralimi
    @126
    @124
    vr
    cK
    wral
    vq
    cK
    wral
    #
    vx
    cV
    wral
    #
    @123
    @124
    vq
    vr
    vx
    cK
    cK
    cV
    ralrot3
    @128
    @127
    @114
    @122
    @75
    @128
    @127
    wi
    @76
    @127
    vx
    cV
    rspn0
    ax-mp
    @34
    @122
    @19
    @49
    @20
    c.pd
    co
    #
    c.x
    co
    #
    @77
    @21
    c.pl
    co
    #
    wceq
    @19
    @115
    c.x
    co
    #
    @77
    @19
    @51
    c.x
    co
    #
    c.pl
    co
    #
    wceq
    vq
    vr
    vw
    @49
    @51
    @82
    cK
    cK
    cV
    vq
    va
    weq
    #
    @31
    @130
    @33
    @131
    @135
    @30
    @129
    @19
    c.x
    @29
    @49
    @20
    c.pd
    oveq1
    oveq2d
    @135
    @32
    @77
    @21
    c.pl
    @29
    @49
    @19
    c.x
    oveq2
    oveq1d
    eqeq12d
    vr
    vb
    weq
    #
    @130
    @132
    @131
    @134
    @136
    @129
    @115
    @19
    c.x
    @20
    @51
    @49
    c.pd
    oveq2
    oveq2d
    @136
    @21
    @133
    @77
    c.pl
    @20
    @51
    @19
    c.x
    oveq2
    oveq2d
    eqeq12d
    vw
    vc
    weq
    #
    @132
    @119
    @134
    @121
    @19
    @82
    @115
    c.x
    oveq1
    @137
    @77
    @87
    @133
    @120
    c.pl
    @19
    @82
    @49
    c.x
    oveq1
    @19
    @82
    @51
    c.x
    oveq1
    oveq12d
    eqeq12d
    rspc3v
    syl5com
    sylbi
    syl
    3ad2ant3
    ax-mp
    @114
    vs
    vv
    @115
    @82
    cK
    cV
    @46
    @119
    c.as
    cvv
    @56
    @114
    rmodislmod.m
    a1i
    #
    @45
    @115
    wceq
    #
    @109
    wa
    @46
    @119
    wceq
    #
    @114
    @109
    @139
    @140
    @44
    @82
    @45
    @115
    c.x
    oveq12
    ancoms
    adantl
    @50
    @113
    @115
    cK
    wcel
    #
    @83
    @62
    @50
    @113
    wa
    @141
    wi
    #
    rmodislmod.r
    @18
    @16
    @142
    @42
    @18
    @70
    @142
    @71
    @70
    @50
    @113
    @141
    cK
    c.pd
    cF
    @49
    @51
    rmodislmod.k
    rmodislmod.p
    grpcl
    3expib
    syl
    3ad2ant2
    ax-mp
    3adant3
    @50
    @113
    @83
    simp3
    #
    @114
    @82
    @115
    c.x
    ovexd
    ovmpt2d
    @114
    @89
    @87
    @117
    @120
    c.pl
    @114
    vs
    vv
    @49
    @82
    cK
    cV
    @46
    @87
    c.as
    cvv
    @138
    @110
    @111
    @114
    @112
    adantl
    @50
    @113
    @83
    simp1
    @143
    @114
    @82
    @49
    c.x
    ovexd
    ovmpt2d
    @114
    vs
    vv
    @51
    @82
    cK
    cV
    @46
    @120
    c.as
    cvv
    @138
    vs
    vb
    weq
    #
    @109
    wa
    @46
    @120
    wceq
    #
    @114
    @109
    @144
    @145
    @44
    @82
    @45
    @51
    c.x
    oveq12
    ancoms
    adantl
    @50
    @113
    @83
    simp2
    @143
    @114
    @82
    @51
    c.x
    ovexd
    ovmpt2d
    oveq12d
    3eqtr4d
    adantl
    vx
    vw
    vv
    c.pl
    c.pd
    cR
    c.x
    c.xp
    c.1
    cF
    c.as
    cK
    cL
    cV
    vs
    vr
    vq
    va
    vb
    vc
    rmodislmod.v
    rmodislmod.a
    rmodislmod.s
    rmodislmod.f
    rmodislmod.k
    rmodislmod.p
    rmodislmod.t
    rmodislmod.u
    rmodislmod.r
    rmodislmod.m
    rmodislmod.l
    rmodislmodlem
    @0
    @49
    cV
    wcel
    #
    wa
    #
    c.1
    @49
    c.as
    co
    @49
    c.1
    c.x
    co
    #
    @49
    @147
    vs
    vv
    c.1
    @49
    cK
    cV
    @46
    @148
    c.as
    cvv
    @56
    @147
    rmodislmod.m
    a1i
    @45
    c.1
    wceq
    #
    vv
    va
    weq
    #
    wa
    @46
    @148
    wceq
    #
    @147
    @150
    @149
    @151
    @44
    @49
    @45
    c.1
    c.x
    oveq12
    ancoms
    adantl
    @0
    c.1
    cK
    wcel
    #
    @146
    @0
    @18
    @152
    @47
    cK
    cF
    c.1
    rmodislmod.k
    rmodislmod.u
    ringidcl
    syl
    adantr
    @0
    @146
    simpr
    @147
    @49
    c.1
    c.x
    ovexd
    ovmpt2d
    @62
    @147
    @148
    @49
    wceq
    #
    wi
    #
    rmodislmod.r
    @42
    @16
    @154
    @18
    @42
    @38
    vw
    cV
    wral
    #
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
    @157
    @154
    @41
    @156
    vq
    vr
    cK
    cK
    @40
    @38
    vx
    vw
    cV
    cV
    @35
    @36
    @38
    simprr
    2ralimi
    2ralimi
    @69
    @158
    @157
    wi
    @72
    @157
    vq
    cK
    rspn0
    ax-mp
    @157
    @156
    @154
    @69
    @157
    @156
    wi
    @72
    @156
    vr
    cK
    rspn0
    ax-mp
    @156
    @155
    @147
    @153
    @75
    @156
    @155
    wi
    @76
    @155
    vx
    cV
    rspn0
    ax-mp
    @146
    @155
    @153
    wi
    @0
    @38
    @153
    vw
    @49
    cV
    vw
    va
    weq
    #
    @37
    @148
    @19
    @49
    @19
    @49
    c.1
    c.x
    oveq1
    @159
    id
    eqeq12d
    rspcv
    adantl
    syl5com
    syl
    3syl
    3ad2ant3
    ax-mp
    eqtrd
    islmodd
end
