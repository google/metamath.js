include "cv.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cfv.mm"
include "wceq.mm"
include "copab.mm"
include "cvv.mm"
include "sectffval.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "opeq12d.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "opabbidv.mm"
include "cxp.mm"
include "ovex.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssexi.mm"
include "a1i.mm"
include "ovmpt2d.mm"

theorem sectfval
  let wph: wff ph
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
  let vx: setvar x
  let vy: setvar y
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
  disjoint .1. f
  disjoint .1. g
  disjoint C f
  disjoint C g
  disjoint f ph
  disjoint g ph
  disjoint H f
  disjoint H g
  disjoint .x. f
  disjoint .x. g
  disjoint X f
  disjoint X g
  disjoint Y f
  disjoint Y g
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c x
  disjoint c y
  disjoint .1. c
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint h x
  disjoint h y
  disjoint .1. h
  disjoint x y
  disjoint .1. x
  disjoint .1. y
  disjoint B c
  disjoint B x
  disjoint B y
  disjoint C c
  disjoint C h
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  disjoint F f
  disjoint F g
  disjoint H c
  disjoint H h
  disjoint H x
  disjoint H y
  disjoint .x. c
  disjoint .x. h
  disjoint .x. x
  disjoint .x. y
  disjoint X x
  disjoint X y
  disjoint G f
  disjoint G g
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( X S Y ) = { <. f , g >. | ( ( f e. ( X H Y ) /\ g e. ( Y H X ) ) /\ ( g ( <. X , Y >. .x. X ) f ) = ( .1. ` X ) ) } )

  proof
    wph
    vx
    vy
    cX
    cY
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
    @2
    @1
    cH
    co
    #
    wcel
    #
    wa
    #
    @5
    @0
    @1
    @2
    cop
    #
    @1
    c.x
    co
    #
    co
    #
    @1
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
    @0
    cX
    cY
    cH
    co
    #
    wcel
    #
    @5
    cY
    cX
    cH
    co
    #
    wcel
    #
    wa
    #
    @5
    @0
    cX
    cY
    cop
    #
    cX
    c.x
    co
    #
    co
    #
    cX
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
    cS
    cvv
    wph
    vx
    vy
    cB
    cC
    cS
    c.x
    c.1
    vf
    vg
    cH
    cX
    cX
    issect.b
    issect.h
    issect.o
    issect.i
    issect.s
    issect.c
    issect.x
    issect.x
    sectffval
    wph
    @1
    cX
    wceq
    #
    @2
    cY
    wceq
    #
    wa
    wa
    #
    @14
    @25
    vf
    vg
    @29
    @8
    @19
    @13
    @24
    @29
    @4
    @16
    @7
    @18
    @29
    @3
    @15
    @0
    @29
    @1
    cX
    @2
    cY
    cH
    wph
    @27
    @28
    simprl
    #
    wph
    @27
    @28
    simprr
    #
    oveq12d
    eleq2d
    @29
    @6
    @17
    @5
    @29
    @2
    cY
    @1
    cX
    cH
    @31
    @30
    oveq12d
    eleq2d
    anbi12d
    @29
    @11
    @22
    @12
    @23
    @29
    @10
    @21
    @5
    @0
    @29
    @9
    @20
    @1
    cX
    c.x
    @29
    @1
    cX
    @2
    cY
    @30
    @31
    opeq12d
    @30
    oveq12d
    oveqd
    @29
    @1
    cX
    c.1
    @30
    fveq2d
    eqeq12d
    anbi12d
    opabbidv
    issect.x
    issect.y
    @26
    cvv
    wcel
    wph
    @26
    @15
    @17
    cxp
    @15
    @17
    cX
    cY
    cH
    ovex
    cY
    cX
    cH
    ovex
    xpex
    @24
    vf
    vg
    @15
    @17
    opabssxp
    ssexi
    a1i
    ovmpt2d
end
