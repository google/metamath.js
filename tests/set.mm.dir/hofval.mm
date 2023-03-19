include "chof.mm"
include "cfv.mm"
include "chomf.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "co.mm"
include "c2nd.mm"
include "cop.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "cbs.mm"
include "chom.mm"
include "cco.mm"
include "csb.mm"
include "ccat.mm"
include "cvv.mm"
include "wceq.mm"
include "df-hof.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "fvexd.mm"
include "syl6eqr.mm"
include "sqxpeqd.mm"
include "simplr.mm"
include "oveqd.mm"
include "fveq1d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "mpt2eq123dv.mm"
include "csbied2.mm"
include "opeq12d.mm"
include "wcel.mm"
include "opex.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem hofval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cH: class H
  let cM: class M
  let vb: setvar b
  let vc: setvar c
  let cF: class F
  let cG: class G
  let cK: class K
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume hofval.m: |- M = ( HomF ` C )
  assume hofval.c: |- ( ph -> C e. Cat )
  assume hofval.b: |- B = ( Base ` C )
  assume hofval.h: |- H = ( Hom ` C )
  assume hofval.o: |- .x. = ( comp ` C )

  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint h x
  disjoint h y
  disjoint B h
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint ph x
  disjoint ph y
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C x
  disjoint C y
  disjoint H f
  disjoint H g
  disjoint H h
  disjoint H x
  disjoint H y
  disjoint .x. f
  disjoint .x. g
  disjoint .x. h
  disjoint .x. x
  disjoint .x. y
  disjoint b c
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint B b
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c x
  disjoint c y
  disjoint B c
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint b ph
  disjoint c ph
  disjoint C b
  disjoint C c
  disjoint H b
  disjoint H c
  disjoint K h
  disjoint W f
  disjoint W g
  disjoint W h
  disjoint W x
  disjoint W y
  disjoint .x. b
  disjoint .x. c
  disjoint X f
  disjoint X g
  disjoint X h
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y g
  disjoint Y h
  disjoint Y x
  disjoint Y y
  disjoint Z f
  disjoint Z g
  disjoint Z h
  disjoint Z x
  disjoint Z y
  assert |- ( ph -> M = <. ( Homf ` C ) , ( x e. ( B X. B ) , y e. ( B X. B ) |-> ( f e. ( ( 1st ` y ) H ( 1st ` x ) ) , g e. ( ( 2nd ` x ) H ( 2nd ` y ) ) |-> ( h e. ( H ` x ) |-> ( ( g ( x .x. ( 2nd ` y ) ) h ) ( <. ( 1st ` y ) , ( 1st ` x ) >. .x. ( 2nd ` y ) ) f ) ) ) ) >. )

  proof
    wph
    cM
    cC
    chof
    cfv
    cC
    chomf
    cfv
    #
    vx
    vy
    cB
    cB
    cxp
    #
    @1
    vf
    vg
    vy
    cv
    #
    c1st
    cfv
    #
    vx
    cv
    #
    c1st
    cfv
    #
    cH
    co
    #
    @4
    c2nd
    cfv
    #
    @2
    c2nd
    cfv
    #
    cH
    co
    #
    vh
    @4
    cH
    cfv
    #
    vg
    cv
    #
    vh
    cv
    #
    @4
    @8
    c.x
    co
    #
    co
    #
    vf
    cv
    #
    @3
    @5
    cop
    #
    @8
    c.x
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    cmpt2
    #
    cop
    #
    hofval.m
    wph
    vc
    cC
    vc
    cv
    #
    chomf
    cfv
    #
    vb
    @23
    cbs
    cfv
    #
    vx
    vy
    vb
    cv
    #
    @26
    cxp
    #
    @27
    vf
    vg
    @3
    @5
    @23
    chom
    cfv
    #
    co
    #
    @7
    @8
    @28
    co
    #
    vh
    @4
    @28
    cfv
    #
    @11
    @12
    @4
    @8
    @23
    cco
    cfv
    #
    co
    #
    co
    #
    @15
    @16
    @8
    @32
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    cmpt2
    #
    csb
    #
    cop
    #
    @22
    ccat
    chof
    cvv
    chof
    vc
    ccat
    @41
    cmpt
    wceq
    wph
    vx
    vy
    vf
    vg
    vh
    vb
    vc
    df-hof
    a1i
    wph
    @23
    cC
    wceq
    #
    wa
    #
    @24
    @0
    @40
    @21
    @43
    @23
    cC
    chomf
    wph
    @42
    simpr
    #
    fveq2d
    @43
    vb
    @25
    cB
    @39
    @21
    cvv
    @43
    @23
    cbs
    fvexd
    @43
    @25
    cC
    cbs
    cfv
    cB
    @43
    @23
    cC
    cbs
    @44
    fveq2d
    hofval.b
    syl6eqr
    @43
    @26
    cB
    wceq
    #
    wa
    #
    vx
    vy
    @27
    @27
    @38
    @1
    @1
    @20
    @46
    @26
    cB
    @43
    @45
    simpr
    sqxpeqd
    #
    @47
    @46
    vf
    vg
    @29
    @30
    @37
    @6
    @9
    @19
    @46
    @28
    cH
    @3
    @5
    @46
    @28
    cC
    chom
    cfv
    cH
    @46
    @23
    cC
    chom
    wph
    @42
    @45
    simplr
    #
    fveq2d
    hofval.h
    syl6eqr
    #
    oveqd
    @46
    @28
    cH
    @7
    @8
    @49
    oveqd
    @46
    vh
    @31
    @36
    @10
    @18
    @46
    @4
    @28
    cH
    @49
    fveq1d
    @46
    @34
    @14
    @15
    @15
    @35
    @17
    @46
    @32
    c.x
    @16
    @8
    @46
    @32
    cC
    cco
    cfv
    c.x
    @46
    @23
    cC
    cco
    @48
    fveq2d
    hofval.o
    syl6eqr
    #
    oveqd
    @46
    @33
    @13
    @11
    @12
    @46
    @32
    c.x
    @4
    @8
    @50
    oveqd
    oveqd
    @46
    @15
    eqidd
    oveq123d
    mpteq12dv
    mpt2eq123dv
    mpt2eq123dv
    csbied2
    opeq12d
    hofval.c
    @22
    cvv
    wcel
    wph
    @0
    @21
    opex
    a1i
    fvmptd
    syl5eq
end
