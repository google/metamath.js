include "cfv.mm"
include "cv.mm"
include "cop.mm"
include "cco.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "crio.mm"
include "eqid.mm"
include "cidval.mm"
include "wreu.mm"
include "wcel.mm"
include "catideu.mm"
include "riotacl.mm"
include "syl.mm"
include "eqeltrd.mm"

theorem catidcl
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.1: class .1.
  let cH: class H
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let c.x: class .x.
  let cY: class Y
  let cF: class F
  assume catidcl.b: |- B = ( Base ` C )
  assume catidcl.h: |- H = ( Hom ` C )
  assume catidcl.i: |- .1. = ( Id ` C )
  assume catidcl.c: |- ( ph -> C e. Cat )
  assume catidcl.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( .1. ` X ) e. ( X H X ) )

  proof
    wph
    cX
    c.1
    cfv
    vg
    cv
    #
    vf
    cv
    #
    vy
    cv
    #
    cX
    cop
    cX
    cC
    cco
    cfv
    #
    co
    co
    @1
    wceq
    vf
    @2
    cX
    cH
    co
    wral
    @1
    @0
    cX
    cX
    cop
    @2
    @3
    co
    co
    @1
    wceq
    vf
    cX
    @2
    cH
    co
    wral
    wa
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
    @5
    wph
    vy
    cB
    cC
    @3
    c.1
    vf
    vg
    cH
    cX
    catidcl.b
    catidcl.h
    @3
    eqid
    #
    catidcl.c
    catidcl.i
    catidcl.x
    cidval
    wph
    @4
    vg
    @5
    wreu
    @6
    @5
    wcel
    wph
    vy
    cB
    cC
    @3
    vf
    vg
    cH
    cX
    catidcl.b
    catidcl.h
    @7
    catidcl.c
    catidcl.x
    catideu
    @4
    vg
    @5
    riotacl
    syl
    eqeltrd
end
