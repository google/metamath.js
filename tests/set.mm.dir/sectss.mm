include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cfv.mm"
include "wceq.mm"
include "copab.mm"
include "cxp.mm"
include "sectfval.mm"
include "opabssxp.mm"
include "syl6eqss.mm"

theorem sectss
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let c.x: class .x.
  let c.1: class .1.
  let cH: class H
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
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


  assert |- ( ph -> ( X S Y ) C_ ( ( X H Y ) X. ( Y H X ) ) )

  proof
    wph
    cX
    cY
    cS
    co
    vf
    cv
    #
    cX
    cY
    cH
    co
    #
    wcel
    vg
    cv
    #
    cY
    cX
    cH
    co
    #
    wcel
    wa
    @2
    @0
    cX
    cY
    cop
    cX
    c.x
    co
    co
    cX
    c.1
    cfv
    wceq
    #
    wa
    vf
    vg
    copab
    @1
    @3
    cxp
    wph
    cB
    cC
    cS
    c.x
    c.1
    vf
    vg
    cH
    cX
    cY
    issect.b
    issect.h
    issect.o
    issect.i
    issect.s
    issect.c
    issect.x
    issect.y
    sectfval
    @4
    vf
    vg
    @1
    @3
    opabssxp
    syl6eqss
end
