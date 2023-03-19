include "cv.mm"
include "cop.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "wcel.mm"
include "cco.mm"
include "cfv.mm"
include "wsbc.mm"
include "chom.mm"
include "cbs.mm"
include "ccat.mm"
include "cvv.mm"
include "fvexd.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "simpl.mm"
include "fveq2d.mm"
include "simpll.mm"
include "simpllr.mm"
include "simplr.mm"
include "oveqd.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "rexeqbidv.mm"
include "eleq12d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "sbcied2.mm"
include "df-cat.mm"
include "elab2g.mm"

theorem iscat
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let vk: setvar k
  let cH: class H
  let cV: class V
  let vb: setvar b
  let vc: setvar c
  let vh: setvar h
  let vo: setvar o
  assume iscat.b: |- B = ( Base ` C )
  assume iscat.h: |- H = ( Hom ` C )
  assume iscat.o: |- .x. = ( comp ` C )

  disjoint f g
  disjoint f k
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint .x. f
  disjoint g k
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint .x. g
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint .x. k
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint .x. w
  disjoint x y
  disjoint x z
  disjoint .x. x
  disjoint y z
  disjoint .x. y
  disjoint .x. z
  disjoint B f
  disjoint B g
  disjoint B k
  disjoint B w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C g
  disjoint C k
  disjoint C w
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint H f
  disjoint H g
  disjoint H k
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b k
  disjoint b o
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint .x. b
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c k
  disjoint c o
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint .x. c
  disjoint f h
  disjoint f o
  disjoint g h
  disjoint g o
  disjoint h k
  disjoint h o
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint .x. h
  disjoint k o
  disjoint o w
  disjoint o x
  disjoint o y
  disjoint o z
  disjoint .x. o
  disjoint B b
  disjoint B c
  disjoint B h
  disjoint B o
  disjoint C b
  disjoint C c
  disjoint C h
  disjoint C o
  disjoint H b
  disjoint H c
  disjoint H h
  disjoint H o
  assert |- ( C e. V -> ( C e. Cat <-> A. x e. B ( E. g e. ( x H x ) A. y e. B ( A. f e. ( y H x ) ( g ( <. y , x >. .x. x ) f ) = f /\ A. f e. ( x H y ) ( f ( <. x , x >. .x. y ) g ) = f ) /\ A. y e. B A. z e. B A. f e. ( x H y ) A. g e. ( y H z ) ( ( g ( <. x , y >. .x. z ) f ) e. ( x H z ) /\ A. w e. B A. k e. ( z H w ) ( ( k ( <. y , z >. .x. w ) g ) ( <. x , y >. .x. w ) f ) = ( k ( <. x , z >. .x. w ) ( g ( <. x , y >. .x. z ) f ) ) ) ) ) )

  proof
    vg
    cv
    #
    vf
    cv
    #
    vy
    cv
    #
    vx
    cv
    #
    cop
    #
    @3
    vo
    cv
    #
    co
    #
    co
    #
    @1
    wceq
    #
    vf
    @2
    @3
    vh
    cv
    #
    co
    #
    wral
    #
    @1
    @0
    @3
    @3
    cop
    #
    @2
    @5
    co
    #
    co
    #
    @1
    wceq
    #
    vf
    @3
    @2
    @9
    co
    #
    wral
    #
    wa
    #
    vy
    vb
    cv
    #
    wral
    #
    vg
    @3
    @3
    @9
    co
    #
    wrex
    #
    @0
    @1
    @3
    @2
    cop
    #
    vz
    cv
    #
    @5
    co
    #
    co
    #
    @3
    @24
    @9
    co
    #
    wcel
    #
    vk
    cv
    #
    @0
    @2
    @24
    cop
    #
    vw
    cv
    #
    @5
    co
    #
    co
    #
    @1
    @23
    @31
    @5
    co
    #
    co
    #
    @29
    @26
    @3
    @24
    cop
    #
    @31
    @5
    co
    #
    co
    #
    wceq
    #
    vk
    @24
    @31
    @9
    co
    #
    wral
    #
    vw
    @19
    wral
    #
    wa
    #
    vg
    @2
    @24
    @9
    co
    #
    wral
    #
    vf
    @16
    wral
    #
    vz
    @19
    wral
    #
    vy
    @19
    wral
    #
    wa
    #
    vx
    @19
    wral
    #
    vo
    vc
    cv
    #
    cco
    cfv
    #
    wsbc
    #
    vh
    @51
    chom
    cfv
    #
    wsbc
    #
    vb
    @51
    cbs
    cfv
    #
    wsbc
    @0
    @1
    @4
    @3
    c.x
    co
    #
    co
    #
    @1
    wceq
    #
    vf
    @2
    @3
    cH
    co
    #
    wral
    #
    @1
    @0
    @12
    @2
    c.x
    co
    #
    co
    #
    @1
    wceq
    #
    vf
    @3
    @2
    cH
    co
    #
    wral
    #
    wa
    #
    vy
    cB
    wral
    #
    vg
    @3
    @3
    cH
    co
    #
    wrex
    #
    @0
    @1
    @23
    @24
    c.x
    co
    #
    co
    #
    @3
    @24
    cH
    co
    #
    wcel
    #
    @29
    @0
    @30
    @31
    c.x
    co
    #
    co
    #
    @1
    @23
    @31
    c.x
    co
    #
    co
    #
    @29
    @72
    @36
    @31
    c.x
    co
    #
    co
    #
    wceq
    #
    vk
    @24
    @31
    cH
    co
    #
    wral
    #
    vw
    cB
    wral
    #
    wa
    #
    vg
    @2
    @24
    cH
    co
    #
    wral
    #
    vf
    @65
    wral
    #
    vz
    cB
    wral
    #
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    wral
    #
    vc
    cC
    ccat
    cV
    @51
    cC
    wceq
    #
    @55
    @92
    vb
    @56
    cB
    cvv
    @93
    @51
    cbs
    fvexd
    @93
    @56
    cC
    cbs
    cfv
    cB
    @51
    cC
    cbs
    fveq2
    iscat.b
    syl6eqr
    @93
    @19
    cB
    wceq
    #
    wa
    #
    @53
    @92
    vh
    @54
    cH
    cvv
    @95
    @51
    chom
    fvexd
    @95
    @54
    cC
    chom
    cfv
    cH
    @95
    @51
    cC
    chom
    @93
    @94
    simpl
    fveq2d
    iscat.h
    syl6eqr
    @95
    @9
    cH
    wceq
    #
    wa
    #
    @50
    @92
    vo
    @52
    c.x
    cvv
    @97
    @51
    cco
    fvexd
    @97
    @52
    cC
    cco
    cfv
    c.x
    @97
    @51
    cC
    cco
    @93
    @94
    @96
    simpll
    fveq2d
    iscat.o
    syl6eqr
    @97
    @5
    c.x
    wceq
    #
    wa
    #
    @49
    @91
    vx
    @19
    cB
    @93
    @94
    @96
    @98
    simpllr
    #
    @99
    @22
    @70
    @48
    @90
    @99
    @20
    @68
    vg
    @21
    @69
    @99
    @9
    cH
    @3
    @3
    @95
    @96
    @98
    simplr
    #
    oveqd
    @99
    @18
    @67
    vy
    @19
    cB
    @100
    @99
    @11
    @61
    @17
    @66
    @99
    @8
    @59
    vf
    @10
    @60
    @99
    @9
    cH
    @2
    @3
    @101
    oveqd
    @99
    @7
    @58
    @1
    @99
    @6
    @57
    @0
    @1
    @99
    @5
    c.x
    @4
    @3
    @97
    @98
    simpr
    #
    oveqd
    oveqd
    eqeq1d
    raleqbidv
    @99
    @15
    @64
    vf
    @16
    @65
    @99
    @9
    cH
    @3
    @2
    @101
    oveqd
    #
    @99
    @14
    @63
    @1
    @99
    @13
    @62
    @1
    @0
    @99
    @5
    c.x
    @12
    @2
    @102
    oveqd
    oveqd
    eqeq1d
    raleqbidv
    anbi12d
    raleqbidv
    rexeqbidv
    @99
    @47
    @89
    vy
    @19
    cB
    @100
    @99
    @46
    @88
    vz
    @19
    cB
    @100
    @99
    @45
    @87
    vf
    @16
    @65
    @103
    @99
    @43
    @85
    vg
    @44
    @86
    @99
    @9
    cH
    @2
    @24
    @101
    oveqd
    @99
    @28
    @74
    @42
    @84
    @99
    @26
    @72
    @27
    @73
    @99
    @25
    @71
    @0
    @1
    @99
    @5
    c.x
    @23
    @24
    @102
    oveqd
    oveqd
    #
    @99
    @9
    cH
    @3
    @24
    @101
    oveqd
    eleq12d
    @99
    @41
    @83
    vw
    @19
    cB
    @100
    @99
    @39
    @81
    vk
    @40
    @82
    @99
    @9
    cH
    @24
    @31
    @101
    oveqd
    @99
    @35
    @78
    @38
    @80
    @99
    @33
    @76
    @1
    @1
    @34
    @77
    @99
    @5
    c.x
    @23
    @31
    @102
    oveqd
    @99
    @32
    @75
    @29
    @0
    @99
    @5
    c.x
    @30
    @31
    @102
    oveqd
    oveqd
    @99
    @1
    eqidd
    oveq123d
    @99
    @29
    @29
    @26
    @72
    @37
    @79
    @99
    @5
    c.x
    @36
    @31
    @102
    oveqd
    @99
    @29
    eqidd
    @104
    oveq123d
    eqeq12d
    raleqbidv
    raleqbidv
    anbi12d
    raleqbidv
    raleqbidv
    raleqbidv
    raleqbidv
    anbi12d
    raleqbidv
    sbcied2
    sbcied2
    sbcied2
    vx
    vy
    vz
    vw
    vf
    vg
    vh
    vk
    vo
    vb
    vc
    df-cat
    elab2g
end
