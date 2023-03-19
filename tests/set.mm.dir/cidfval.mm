include "ccid.mm"
include "cfv.mm"
include "cv.mm"
include "cop.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "crio.mm"
include "cmpt.mm"
include "ccat.mm"
include "wcel.mm"
include "cbs.mm"
include "chom.mm"
include "cco.mm"
include "csb.mm"
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
include "riotaeqbidv.mm"
include "mpteq12dv.mm"
include "csbied2.mm"
include "df-cid.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem cidfval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let c.1: class .1.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let vb: setvar b
  let vc: setvar c
  let vh: setvar h
  let vo: setvar o
  let cX: class X
  assume cidfval.b: |- B = ( Base ` C )
  assume cidfval.h: |- H = ( Hom ` C )
  assume cidfval.o: |- .x. = ( comp ` C )
  assume cidfval.c: |- ( ph -> C e. Cat )
  assume cidfval.i: |- .1. = ( Id ` C )

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint .x. f
  disjoint .x. g
  disjoint .x. x
  disjoint .x. y
  disjoint H f
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint f ph
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b o
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c o
  disjoint c x
  disjoint c y
  disjoint B c
  disjoint f h
  disjoint f o
  disjoint g h
  disjoint g o
  disjoint h o
  disjoint h x
  disjoint h y
  disjoint B h
  disjoint o x
  disjoint o y
  disjoint B o
  disjoint C b
  disjoint C c
  disjoint C h
  disjoint C o
  disjoint .x. b
  disjoint .x. c
  disjoint .x. h
  disjoint .x. o
  disjoint H b
  disjoint H c
  disjoint H h
  disjoint H o
  disjoint X f
  disjoint X g
  disjoint X x
  disjoint X y
  assert |- ( ph -> .1. = ( x e. B |-> ( iota_ g e. ( x H x ) A. y e. B ( A. f e. ( y H x ) ( g ( <. y , x >. .x. x ) f ) = f /\ A. f e. ( x H y ) ( f ( <. x , x >. .x. y ) g ) = f ) ) ) )

  proof
    wph
    c.1
    cC
    ccid
    cfv
    #
    vx
    cB
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
    @4
    c.x
    co
    #
    co
    #
    @2
    wceq
    #
    vf
    @3
    @4
    cH
    co
    #
    wral
    #
    @2
    @1
    @4
    @4
    cop
    #
    @3
    c.x
    co
    #
    co
    #
    @2
    wceq
    #
    vf
    @4
    @3
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
    @4
    @4
    cH
    co
    #
    crio
    #
    cmpt
    #
    cidfval.i
    wph
    cC
    ccat
    wcel
    @0
    @21
    wceq
    cidfval.c
    vc
    cC
    vb
    vc
    cv
    #
    cbs
    cfv
    #
    vh
    @22
    chom
    cfv
    #
    vo
    @22
    cco
    cfv
    #
    vx
    vb
    cv
    #
    @1
    @2
    @5
    @4
    vo
    cv
    #
    co
    #
    co
    #
    @2
    wceq
    #
    vf
    @3
    @4
    vh
    cv
    #
    co
    #
    wral
    #
    @2
    @1
    @11
    @3
    @27
    co
    #
    co
    #
    @2
    wceq
    #
    vf
    @4
    @3
    @31
    co
    #
    wral
    #
    wa
    #
    vy
    @26
    wral
    #
    vg
    @4
    @4
    @31
    co
    #
    crio
    #
    cmpt
    #
    csb
    #
    csb
    #
    csb
    @21
    ccat
    ccid
    @22
    cC
    wceq
    #
    vb
    @23
    cB
    @45
    @21
    cvv
    @46
    @22
    cbs
    fvexd
    @46
    @23
    cC
    cbs
    cfv
    #
    cB
    @22
    cC
    cbs
    fveq2
    cidfval.b
    syl6eqr
    @46
    @26
    cB
    wceq
    #
    wa
    #
    vh
    @24
    cH
    @44
    @21
    cvv
    @49
    @22
    chom
    fvexd
    @49
    @24
    cC
    chom
    cfv
    cH
    @49
    @22
    cC
    chom
    @46
    @48
    simpl
    fveq2d
    cidfval.h
    syl6eqr
    @49
    @31
    cH
    wceq
    #
    wa
    #
    vo
    @25
    c.x
    @43
    @21
    cvv
    @51
    @22
    cco
    fvexd
    @51
    @25
    cC
    cco
    cfv
    c.x
    @51
    @22
    cC
    cco
    @46
    @48
    @50
    simpll
    fveq2d
    cidfval.o
    syl6eqr
    @51
    @27
    c.x
    wceq
    #
    wa
    #
    vx
    @26
    @42
    cB
    @20
    @46
    @48
    @50
    @52
    simpllr
    #
    @53
    @40
    @18
    vg
    @41
    @19
    @53
    @31
    cH
    @4
    @4
    @49
    @50
    @52
    simplr
    #
    oveqd
    @53
    @39
    @17
    vy
    @26
    cB
    @54
    @53
    @33
    @10
    @38
    @16
    @53
    @30
    @8
    vf
    @32
    @9
    @53
    @31
    cH
    @3
    @4
    @55
    oveqd
    @53
    @29
    @7
    @2
    @53
    @28
    @6
    @1
    @2
    @53
    @27
    c.x
    @5
    @4
    @51
    @52
    simpr
    #
    oveqd
    oveqd
    eqeq1d
    raleqbidv
    @53
    @36
    @14
    vf
    @37
    @15
    @53
    @31
    cH
    @4
    @3
    @55
    oveqd
    @53
    @35
    @13
    @2
    @53
    @34
    @12
    @2
    @1
    @53
    @27
    c.x
    @11
    @3
    @56
    oveqd
    oveqd
    eqeq1d
    raleqbidv
    anbi12d
    raleqbidv
    riotaeqbidv
    mpteq12dv
    csbied2
    csbied2
    csbied2
    vx
    vy
    vf
    vg
    vh
    vo
    vb
    vc
    df-cid
    vx
    cB
    @20
    cB
    @47
    cvv
    cidfval.b
    cC
    cbs
    fvex
    eqeltri
    mptex
    fvmpt
    syl
    syl5eq
end
