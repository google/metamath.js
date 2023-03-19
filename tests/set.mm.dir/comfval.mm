include "co.mm"
include "cv.mm"
include "cop.mm"
include "cvv.mm"
include "comffval.mm"
include "wceq.mm"
include "wa.mm"
include "oveq12.mm"
include "adantl.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem comfval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let c.x: class .x.
  let cF: class F
  let cG: class G
  let cH: class H
  let cO: class O
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  assume comfffval.o: |- O = ( comf ` C )
  assume comfffval.b: |- B = ( Base ` C )
  assume comfffval.h: |- H = ( Hom ` C )
  assume comfffval.x: |- .x. = ( comp ` C )
  assume comffval.x: |- ( ph -> X e. B )
  assume comffval.y: |- ( ph -> Y e. B )
  assume comffval.z: |- ( ph -> Z e. B )
  assume comfval.f: |- ( ph -> F e. ( X H Y ) )
  assume comfval.g: |- ( ph -> G e. ( Y H Z ) )


  assert |- ( ph -> ( G ( <. X , Y >. O Z ) F ) = ( G ( <. X , Y >. .x. Z ) F ) )

  proof
    wph
    vg
    vf
    cG
    cF
    cY
    cZ
    cH
    co
    cX
    cY
    cH
    co
    vg
    cv
    #
    vf
    cv
    #
    cX
    cY
    cop
    #
    cZ
    c.x
    co
    #
    co
    #
    cG
    cF
    @3
    co
    #
    @2
    cZ
    cO
    co
    cvv
    wph
    cB
    cC
    c.x
    vf
    vg
    cH
    cO
    cX
    cY
    cZ
    comfffval.o
    comfffval.b
    comfffval.h
    comfffval.x
    comffval.x
    comffval.y
    comffval.z
    comffval
    @0
    cG
    wceq
    @1
    cF
    wceq
    wa
    @4
    @5
    wceq
    wph
    @0
    cG
    @1
    cF
    @3
    oveq12
    adantl
    comfval.g
    comfval.f
    wph
    cG
    cF
    @3
    ovexd
    ovmpt2d
end
