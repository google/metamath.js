include "cv.mm"
include "cop.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "crio.mm"
include "cvv.mm"
include "cidfval.mm"
include "simpr.mm"
include "oveq12d.mm"
include "oveq2d.mm"
include "opeq2d.mm"
include "oveqd.mm"
include "eqeq1d.mm"
include "raleqbidv.mm"
include "oveq1d.mm"
include "opeq12d.mm"
include "anbi12d.mm"
include "ralbidv.mm"
include "riotaeqbidv.mm"
include "wcel.mm"
include "riotaex.mm"
include "a1i.mm"
include "fvmptd.mm"

theorem cidval
  let wph: wff ph
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let c.1: class .1.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cX: class X
  let vb: setvar b
  let vc: setvar c
  let vh: setvar h
  let vo: setvar o
  let vx: setvar x
  assume cidfval.b: |- B = ( Base ` C )
  assume cidfval.h: |- H = ( Hom ` C )
  assume cidfval.o: |- .x. = ( comp ` C )
  assume cidfval.c: |- ( ph -> C e. Cat )
  assume cidfval.i: |- .1. = ( Id ` C )
  assume cidval.x: |- ( ph -> X e. B )

  disjoint f g
  disjoint f y
  disjoint B f
  disjoint g y
  disjoint B g
  disjoint B y
  disjoint C f
  disjoint C g
  disjoint C y
  disjoint .x. f
  disjoint .x. g
  disjoint .x. y
  disjoint H f
  disjoint H g
  disjoint H y
  disjoint f ph
  disjoint g ph
  disjoint ph y
  disjoint X f
  disjoint X g
  disjoint X y
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
  disjoint f x
  disjoint g h
  disjoint g o
  disjoint g x
  disjoint h o
  disjoint h x
  disjoint h y
  disjoint B h
  disjoint o x
  disjoint o y
  disjoint B o
  disjoint x y
  disjoint B x
  disjoint C b
  disjoint C c
  disjoint C h
  disjoint C o
  disjoint C x
  disjoint .x. b
  disjoint .x. c
  disjoint .x. h
  disjoint .x. o
  disjoint .x. x
  disjoint H b
  disjoint H c
  disjoint H h
  disjoint H o
  disjoint H x
  disjoint ph x
  disjoint X x
  assert |- ( ph -> ( .1. ` X ) = ( iota_ g e. ( X H X ) A. y e. B ( A. f e. ( y H X ) ( g ( <. y , X >. .x. X ) f ) = f /\ A. f e. ( X H y ) ( f ( <. X , X >. .x. y ) g ) = f ) ) )

  proof
    wph
    vx
    cX
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
    @3
    @3
    cop
    #
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
    crio
    @0
    @1
    @2
    cX
    cop
    #
    cX
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
    cX
    cH
    co
    #
    wral
    #
    @1
    @0
    cX
    cX
    cop
    #
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
    cX
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
    cX
    cX
    cH
    co
    #
    crio
    #
    cB
    c.1
    cvv
    wph
    vx
    vy
    cB
    cC
    c.x
    c.1
    vf
    vg
    cH
    cidfval.b
    cidfval.h
    cidfval.o
    cidfval.c
    cidfval.i
    cidfval
    wph
    @3
    cX
    wceq
    #
    wa
    #
    @17
    @32
    vg
    @18
    @33
    @36
    @3
    cX
    @3
    cX
    cH
    wph
    @35
    simpr
    #
    @37
    oveq12d
    @36
    @16
    @31
    vy
    cB
    @36
    @9
    @24
    @15
    @30
    @36
    @7
    @22
    vf
    @8
    @23
    @36
    @3
    cX
    @2
    cH
    @37
    oveq2d
    @36
    @6
    @21
    @1
    @36
    @5
    @20
    @0
    @1
    @36
    @4
    @19
    @3
    cX
    c.x
    @36
    @3
    cX
    @2
    @37
    opeq2d
    @37
    oveq12d
    oveqd
    eqeq1d
    raleqbidv
    @36
    @13
    @28
    vf
    @14
    @29
    @36
    @3
    cX
    @2
    cH
    @37
    oveq1d
    @36
    @12
    @27
    @1
    @36
    @11
    @26
    @1
    @0
    @36
    @10
    @25
    @2
    c.x
    @36
    @3
    cX
    @3
    cX
    @37
    @37
    opeq12d
    oveq1d
    oveqd
    eqeq1d
    raleqbidv
    anbi12d
    ralbidv
    riotaeqbidv
    cidval.x
    @34
    cvv
    wcel
    wph
    @32
    vg
    @33
    riotaex
    a1i
    fvmptd
end
