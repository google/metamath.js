include "csect.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "copab.mm"
include "cmpt2.mm"
include "ccat.mm"
include "cbs.mm"
include "cco.mm"
include "ccid.mm"
include "chom.mm"
include "wsbc.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "cvv.mm"
include "fvexd.mm"
include "simpr.mm"
include "oveqd.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "simpl.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqeq12d.mm"
include "sbcied2.mm"
include "opabbidv.mm"
include "mpt2eq123dv.mm"
include "df-sect.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mpt2ex.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl5eq.mm"

theorem sectffval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vh: setvar h
  let cF: class F
  let cG: class G
  assume issect.b: |- B = ( Base ` C )
  assume issect.h: |- H = ( Hom ` C )
  assume issect.o: |- .x. = ( comp ` C )
  assume issect.i: |- .1. = ( Id ` C )
  assume issect.s: |- S = ( Sect ` C )
  assume issect.c: |- ( ph -> C e. Cat )
  assume issect.x: |- ( ph -> X e. B )
  assume issect.y: |- ( ph -> Y e. B )

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint .1. f
  disjoint g x
  disjoint g y
  disjoint .1. g
  disjoint x y
  disjoint .1. x
  disjoint .1. y
  disjoint B x
  disjoint B y
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint f ph
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint H f
  disjoint H g
  disjoint H x
  disjoint H y
  disjoint .x. f
  disjoint .x. g
  disjoint .x. x
  disjoint .x. y
  disjoint X f
  disjoint X g
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y g
  disjoint Y x
  disjoint Y y
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c x
  disjoint c y
  disjoint .1. c
  disjoint f h
  disjoint g h
  disjoint h x
  disjoint h y
  disjoint .1. h
  disjoint B c
  disjoint C c
  disjoint C h
  disjoint F f
  disjoint F g
  disjoint H c
  disjoint H h
  disjoint .x. c
  disjoint .x. h
  disjoint G f
  disjoint G g
  assert |- ( ph -> S = ( x e. B , y e. B |-> { <. f , g >. | ( ( f e. ( x H y ) /\ g e. ( y H x ) ) /\ ( g ( <. x , y >. .x. x ) f ) = ( .1. ` x ) ) } ) )

  proof
    wph
    cS
    cC
    csect
    cfv
    #
    vx
    vy
    cB
    cB
    vf
    cv
    #
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    wcel
    #
    vg
    cv
    #
    @3
    @2
    cH
    co
    #
    wcel
    #
    wa
    #
    @6
    @1
    @2
    @3
    cop
    #
    @2
    c.x
    co
    #
    co
    #
    @2
    c.1
    cfv
    #
    wceq
    #
    wa
    #
    vf
    vg
    copab
    #
    cmpt2
    #
    issect.s
    wph
    cC
    ccat
    wcel
    @0
    @17
    wceq
    issect.c
    vc
    cC
    vx
    vy
    vc
    cv
    #
    cbs
    cfv
    #
    @19
    @1
    @2
    @3
    vh
    cv
    #
    co
    #
    wcel
    #
    @6
    @3
    @2
    @20
    co
    #
    wcel
    #
    wa
    #
    @6
    @1
    @10
    @2
    @18
    cco
    cfv
    #
    co
    #
    co
    #
    @2
    @18
    ccid
    cfv
    #
    cfv
    #
    wceq
    #
    wa
    #
    vh
    @18
    chom
    cfv
    #
    wsbc
    #
    vf
    vg
    copab
    #
    cmpt2
    @17
    ccat
    csect
    @18
    cC
    wceq
    #
    vx
    vy
    @19
    @19
    @35
    cB
    cB
    @16
    @36
    @19
    cC
    cbs
    cfv
    #
    cB
    @18
    cC
    cbs
    fveq2
    issect.b
    syl6eqr
    #
    @38
    @36
    @34
    @15
    vf
    vg
    @36
    @32
    @15
    vh
    @33
    cH
    cvv
    @36
    @18
    chom
    fvexd
    @36
    @33
    cC
    chom
    cfv
    cH
    @18
    cC
    chom
    fveq2
    issect.h
    syl6eqr
    @36
    @20
    cH
    wceq
    #
    wa
    #
    @25
    @9
    @31
    @14
    @40
    @22
    @5
    @24
    @8
    @40
    @21
    @4
    @1
    @40
    @20
    cH
    @2
    @3
    @36
    @39
    simpr
    #
    oveqd
    eleq2d
    @40
    @23
    @7
    @6
    @40
    @20
    cH
    @3
    @2
    @41
    oveqd
    eleq2d
    anbi12d
    @40
    @28
    @12
    @30
    @13
    @40
    @27
    @11
    @6
    @1
    @40
    @26
    c.x
    @10
    @2
    @40
    @26
    cC
    cco
    cfv
    c.x
    @40
    @18
    cC
    cco
    @36
    @39
    simpl
    #
    fveq2d
    issect.o
    syl6eqr
    oveqd
    oveqd
    @40
    @2
    @29
    c.1
    @40
    @29
    cC
    ccid
    cfv
    c.1
    @40
    @18
    cC
    ccid
    @42
    fveq2d
    issect.i
    syl6eqr
    fveq1d
    eqeq12d
    anbi12d
    sbcied2
    opabbidv
    mpt2eq123dv
    vx
    vy
    vf
    vg
    vh
    vc
    df-sect
    vx
    vy
    cB
    cB
    @16
    cB
    @37
    cvv
    issect.b
    cC
    cbs
    fvex
    eqeltri
    #
    @43
    mpt2ex
    fvmpt
    syl
    syl5eq
end
