include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cmnd.mm"
include "cfv.mm"
include "simpllr.mm"
include "simpr.mm"
include "oveq12d.mm"
include "simp-5l.mm"
include "syl3an1.mm"
include "simp-4r.mm"
include "simplr.mm"
include "mhmlem.mm"
include "wf.mm"
include "wfo.mm"
include "fof.mm"
include "syl.mm"
include "ad5antr.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "ffvelrnd.mm"
include "eqeltrrd.mm"
include "foelrni.mm"
include "syl2an.mm"
include "ad2antrr.mm"
include "r19.29a.mm"
include "simpl.mm"
include "simpll.mm"
include "simplrl.mm"
include "simplrr.mm"
include "w3a.mm"
include "simp-6r.mm"
include "mndass.mm"
include "syl13anc.mm"
include "fveq2d.mm"
include "simp-7l.mm"
include "3eqtr3d.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "simp-5r.mm"
include "sylan.mm"
include "3ad2antr3.mm"
include "ad4antr.mm"
include "3adantr3.mm"
include "ralrimiva.mm"
include "jca.mm"
include "ralrimivva.mm"
include "c0g.mm"
include "eqid.mm"
include "mndidcl.mm"
include "simplll.mm"
include "ad3antrrr.mm"
include "mndlid.mm"
include "syl2anc.mm"
include "eqtr3d.mm"
include "mndrid.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "ismnd.mm"
include "sylanbrc.mm"

theorem mhmmnd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let c.pd: class .+^
  let cF: class F
  let cG: class G
  let cH: class H
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vd: setvar d
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vb: setvar b
  let vc: setvar c
  assume ghmgrp.f: |- ( ( ph /\ x e. X /\ y e. X ) -> ( F ` ( x .+ y ) ) = ( ( F ` x ) .+^ ( F ` y ) ) )
  assume ghmgrp.x: |- X = ( Base ` G )
  assume ghmgrp.y: |- Y = ( Base ` H )
  assume ghmgrp.p: |- .+ = ( +g ` G )
  assume ghmgrp.q: |- .+^ = ( +g ` H )
  assume ghmgrp.1: |- ( ph -> F : X -onto-> Y )
  assume mhmmnd.3: |- ( ph -> G e. Mnd )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint .+ x
  disjoint .+ y
  disjoint H x
  disjoint H y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint .+^ x
  disjoint .+^ y
  disjoint ph x
  disjoint ph y
  disjoint F a
  disjoint F d
  disjoint F f
  disjoint F i
  disjoint F j
  disjoint F k
  disjoint a d
  disjoint a f
  disjoint a i
  disjoint a j
  disjoint a k
  disjoint a x
  disjoint a y
  disjoint d f
  disjoint d i
  disjoint d j
  disjoint d k
  disjoint d x
  disjoint d y
  disjoint f i
  disjoint f j
  disjoint f k
  disjoint f x
  disjoint f y
  disjoint i j
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint j k
  disjoint j x
  disjoint j y
  disjoint k x
  disjoint k y
  disjoint G a
  disjoint G d
  disjoint G f
  disjoint G i
  disjoint G j
  disjoint G k
  disjoint .+ i
  disjoint .+ j
  disjoint .+ k
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H d
  disjoint H f
  disjoint H i
  disjoint a b
  disjoint a c
  disjoint b c
  disjoint b d
  disjoint b f
  disjoint b i
  disjoint b x
  disjoint b y
  disjoint c d
  disjoint c f
  disjoint c i
  disjoint c x
  disjoint c y
  disjoint X i
  disjoint X j
  disjoint X k
  disjoint Y a
  disjoint Y b
  disjoint Y c
  disjoint Y d
  disjoint Y f
  disjoint Y i
  disjoint Y j
  disjoint Y k
  disjoint b j
  disjoint b k
  disjoint c j
  disjoint c k
  disjoint .+^ a
  disjoint .+^ b
  disjoint .+^ c
  disjoint .+^ d
  disjoint .+^ f
  disjoint .+^ i
  disjoint .+^ j
  disjoint .+^ k
  disjoint a ph
  disjoint b ph
  disjoint c ph
  disjoint i ph
  disjoint j ph
  disjoint k ph
  assert |- ( ph -> H e. Mnd )

  proof
    wph
    va
    cv
    #
    vb
    cv
    #
    c.pd
    co
    #
    cY
    wcel
    #
    @2
    vc
    cv
    #
    c.pd
    co
    #
    @0
    @1
    @4
    c.pd
    co
    #
    c.pd
    co
    #
    wceq
    #
    vc
    cY
    wral
    #
    wa
    #
    vb
    cY
    wral
    va
    cY
    wral
    vd
    cv
    #
    @0
    c.pd
    co
    #
    @0
    wceq
    #
    @0
    @11
    c.pd
    co
    #
    @0
    wceq
    #
    wa
    #
    va
    cY
    wral
    #
    vd
    cY
    wrex
    #
    cH
    cmnd
    wcel
    wph
    @10
    va
    vb
    cY
    cY
    wph
    @0
    cY
    wcel
    #
    @1
    cY
    wcel
    #
    wa
    #
    wa
    #
    @3
    @9
    @22
    vi
    cv
    #
    cF
    cfv
    #
    @0
    wceq
    #
    @3
    vi
    cX
    @22
    @23
    cX
    wcel
    #
    wa
    #
    @25
    wa
    #
    vj
    cv
    #
    cF
    cfv
    #
    @1
    wceq
    #
    @3
    vj
    cX
    @28
    @29
    cX
    wcel
    #
    wa
    #
    @31
    wa
    #
    @24
    @30
    c.pd
    co
    #
    @2
    cY
    @34
    @24
    @0
    @30
    @1
    c.pd
    @27
    @25
    @32
    @31
    simpllr
    @33
    @31
    simpr
    oveq12d
    @34
    @23
    @29
    c.pl
    co
    #
    cF
    cfv
    #
    @35
    cY
    @34
    vx
    vy
    @23
    @29
    c.pl
    c.pd
    cF
    cX
    @34
    wph
    vx
    cv
    #
    cX
    wcel
    #
    vy
    cv
    #
    cX
    wcel
    #
    @38
    @40
    c.pl
    co
    cF
    cfv
    @38
    cF
    cfv
    @40
    cF
    cfv
    c.pd
    co
    wceq
    #
    wph
    @21
    @26
    @25
    @32
    @31
    simp-5l
    ghmgrp.f
    syl3an1
    @22
    @26
    @25
    @32
    @31
    simp-4r
    #
    @28
    @32
    @31
    simplr
    #
    mhmlem
    @34
    cX
    cY
    @36
    cF
    wph
    cX
    cY
    cF
    wf
    #
    @21
    @26
    @25
    @32
    @31
    wph
    cX
    cY
    cF
    wfo
    #
    @45
    ghmgrp.1
    cX
    cY
    cF
    fof
    syl
    #
    ad5antr
    @34
    cG
    cmnd
    wcel
    #
    @26
    @32
    @36
    cX
    wcel
    #
    wph
    @48
    @21
    @26
    @25
    @32
    @31
    mhmmnd.3
    ad5antr
    @43
    @44
    cX
    c.pl
    cG
    @23
    @29
    ghmgrp.x
    ghmgrp.p
    mndcl
    #
    syl3anc
    ffvelrnd
    eqeltrrd
    eqeltrrd
    @22
    @31
    vj
    cX
    wrex
    #
    @26
    @25
    wph
    @46
    @20
    @51
    @21
    ghmgrp.1
    @19
    @20
    simpr
    vj
    cX
    cY
    cF
    @1
    foelrni
    syl2an
    #
    ad2antrr
    r19.29a
    wph
    @46
    @19
    @25
    vi
    cX
    wrex
    #
    @21
    ghmgrp.1
    @19
    @20
    simpl
    vi
    cX
    cY
    cF
    @0
    foelrni
    #
    syl2an
    #
    r19.29a
    @22
    @8
    vc
    cY
    @22
    @4
    cY
    wcel
    #
    wa
    wph
    @19
    @20
    @56
    @8
    wph
    @21
    @56
    simpll
    wph
    @19
    @20
    @56
    simplrl
    wph
    @19
    @20
    @56
    simplrr
    @22
    @56
    simpr
    wph
    @19
    @20
    @56
    w3a
    #
    wa
    #
    @25
    @8
    vi
    cX
    @58
    @26
    wa
    #
    @25
    wa
    #
    @31
    @8
    vj
    cX
    @60
    @32
    wa
    #
    @31
    wa
    #
    vk
    cv
    #
    cF
    cfv
    #
    @4
    wceq
    #
    @8
    vk
    cX
    @62
    @63
    cX
    wcel
    #
    wa
    #
    @65
    wa
    #
    @35
    @64
    c.pd
    co
    #
    @24
    @30
    @64
    c.pd
    co
    #
    c.pd
    co
    #
    @5
    @7
    @68
    @37
    @64
    c.pd
    co
    #
    @24
    @29
    @63
    c.pl
    co
    #
    cF
    cfv
    #
    c.pd
    co
    #
    @69
    @71
    @68
    @36
    @63
    c.pl
    co
    #
    cF
    cfv
    @23
    @73
    c.pl
    co
    #
    cF
    cfv
    @72
    @75
    @68
    @76
    @77
    cF
    @68
    @48
    @26
    @32
    @66
    @76
    @77
    wceq
    @59
    @48
    @25
    @32
    @31
    @66
    @65
    wph
    @48
    @57
    @26
    mhmmnd.3
    ad2antrr
    ad5antr
    #
    @58
    @26
    @25
    @32
    @31
    @66
    @65
    simp-6r
    #
    @60
    @32
    @31
    @66
    @65
    simp-4r
    #
    @62
    @66
    @65
    simplr
    #
    cX
    c.pl
    cG
    @23
    @29
    @63
    ghmgrp.x
    ghmgrp.p
    mndass
    syl13anc
    fveq2d
    @68
    vx
    vy
    @36
    @63
    c.pl
    c.pd
    cF
    cX
    @68
    wph
    @39
    @41
    @42
    wph
    @57
    @26
    @25
    @32
    @31
    @66
    @65
    simp-7l
    #
    ghmgrp.f
    syl3an1
    #
    @68
    @48
    @26
    @32
    @49
    @78
    @79
    @80
    @50
    syl3anc
    @81
    mhmlem
    @68
    vx
    vy
    @23
    @73
    c.pl
    c.pd
    cF
    cX
    @83
    @79
    @68
    @48
    @32
    @66
    @73
    cX
    wcel
    @78
    @80
    @81
    cX
    c.pl
    cG
    @29
    @63
    ghmgrp.x
    ghmgrp.p
    mndcl
    syl3anc
    mhmlem
    3eqtr3d
    @68
    @37
    @35
    @64
    c.pd
    @68
    wph
    @26
    @32
    @37
    @35
    wceq
    @82
    @79
    @80
    wph
    @26
    @32
    w3a
    #
    vx
    vy
    @23
    @29
    c.pl
    c.pd
    cF
    cX
    @84
    wph
    @39
    @41
    @42
    wph
    @26
    @32
    simp1
    ghmgrp.f
    syl3an1
    wph
    @26
    @32
    simp2
    wph
    @26
    @32
    simp3
    mhmlem
    syl3anc
    oveq1d
    @68
    @74
    @70
    @24
    c.pd
    @68
    vx
    vy
    @29
    @63
    c.pl
    c.pd
    cF
    cX
    @83
    @80
    @81
    mhmlem
    oveq2d
    3eqtr3d
    @68
    @35
    @2
    @64
    @4
    c.pd
    @68
    @24
    @0
    @30
    @1
    c.pd
    @59
    @25
    @32
    @31
    @66
    @65
    simp-5r
    #
    @61
    @31
    @66
    @65
    simpllr
    #
    oveq12d
    @67
    @65
    simpr
    #
    oveq12d
    @68
    @24
    @0
    @70
    @6
    c.pd
    @85
    @68
    @30
    @1
    @64
    @4
    c.pd
    @86
    @87
    oveq12d
    oveq12d
    3eqtr3d
    @58
    @65
    vk
    cX
    wrex
    #
    @26
    @25
    @32
    @31
    wph
    @19
    @56
    @88
    @20
    wph
    @46
    @56
    @88
    ghmgrp.1
    vk
    cX
    cY
    cF
    @4
    foelrni
    sylan
    3ad2antr3
    ad4antr
    r19.29a
    @58
    @51
    @26
    @25
    wph
    @19
    @20
    @51
    @56
    @52
    3adantr3
    ad2antrr
    r19.29a
    wph
    @19
    @20
    @53
    @56
    @55
    3adantr3
    r19.29a
    syl13anc
    ralrimiva
    jca
    ralrimivva
    wph
    cG
    c0g
    cfv
    #
    cF
    cfv
    #
    cY
    wcel
    @90
    @0
    c.pd
    co
    #
    @0
    wceq
    #
    @0
    @90
    c.pd
    co
    #
    @0
    wceq
    #
    wa
    #
    va
    cY
    wral
    #
    @18
    wph
    cX
    cY
    @89
    cF
    @47
    wph
    @48
    @89
    cX
    wcel
    #
    mhmmnd.3
    cX
    cG
    @89
    ghmgrp.x
    @89
    eqid
    #
    mndidcl
    #
    syl
    ffvelrnd
    wph
    @95
    va
    cY
    wph
    @19
    wa
    #
    @25
    @95
    vi
    cX
    @100
    @26
    wa
    #
    @25
    wa
    #
    @92
    @94
    @102
    @90
    @24
    c.pd
    co
    #
    @24
    @91
    @0
    @102
    @89
    @23
    c.pl
    co
    #
    cF
    cfv
    @103
    @24
    @102
    vx
    vy
    @89
    @23
    c.pl
    c.pd
    cF
    cX
    @102
    wph
    @39
    @41
    @42
    wph
    @19
    @26
    @25
    simplll
    ghmgrp.f
    syl3an1
    #
    @102
    @48
    @97
    wph
    @48
    @19
    @26
    @25
    mhmmnd.3
    ad3antrrr
    #
    @99
    syl
    #
    @100
    @26
    @25
    simplr
    #
    mhmlem
    @102
    @104
    @23
    cF
    @102
    @48
    @26
    @104
    @23
    wceq
    @106
    @108
    cX
    c.pl
    cG
    @23
    @89
    ghmgrp.x
    ghmgrp.p
    @98
    mndlid
    syl2anc
    fveq2d
    eqtr3d
    @102
    @24
    @0
    @90
    c.pd
    @101
    @25
    simpr
    #
    oveq2d
    @109
    3eqtr3d
    @102
    @24
    @90
    c.pd
    co
    #
    @24
    @93
    @0
    @102
    @23
    @89
    c.pl
    co
    #
    cF
    cfv
    @110
    @24
    @102
    vx
    vy
    @23
    @89
    c.pl
    c.pd
    cF
    cX
    @105
    @108
    @107
    mhmlem
    @102
    @111
    @23
    cF
    @102
    @48
    @26
    @111
    @23
    wceq
    @106
    @108
    cX
    c.pl
    cG
    @23
    @89
    ghmgrp.x
    ghmgrp.p
    @98
    mndrid
    syl2anc
    fveq2d
    eqtr3d
    @102
    @24
    @0
    @90
    c.pd
    @109
    oveq1d
    @109
    3eqtr3d
    jca
    wph
    @46
    @19
    @53
    ghmgrp.1
    @54
    sylan
    r19.29a
    ralrimiva
    @17
    @96
    vd
    @90
    cY
    @11
    @90
    wceq
    #
    @16
    @95
    va
    cY
    @112
    @13
    @92
    @15
    @94
    @112
    @12
    @91
    @0
    @11
    @90
    @0
    c.pd
    oveq1
    eqeq1d
    @112
    @14
    @93
    @0
    @11
    @90
    @0
    c.pd
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    rspcev
    syl2anc
    cY
    c.pd
    vd
    cH
    va
    vb
    vc
    ghmgrp.y
    ghmgrp.q
    ismnd
    sylanbrc
end
