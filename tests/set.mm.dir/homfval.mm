include "cv.mm"
include "co.mm"
include "cvv.mm"
include "cmpt2.mm"
include "wceq.mm"
include "homffval.mm"
include "a1i.mm"
include "wa.mm"
include "oveq12.mm"
include "adantl.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem homfval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cF: class F
  let cH: class H
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  assume homffval.f: |- F = ( Homf ` C )
  assume homffval.b: |- B = ( Base ` C )
  assume homffval.h: |- H = ( Hom ` C )
  assume homfval.x: |- ( ph -> X e. B )
  assume homfval.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X F Y ) = ( X H Y ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    cH
    co
    #
    cX
    cY
    cH
    co
    #
    cF
    cvv
    cF
    vx
    vy
    cB
    cB
    @2
    cmpt2
    wceq
    wph
    vx
    vy
    cB
    cC
    cF
    cH
    homffval.f
    homffval.b
    homffval.h
    homffval
    a1i
    @0
    cX
    wceq
    @1
    cY
    wceq
    wa
    @2
    @3
    wceq
    wph
    @0
    cX
    @1
    cY
    cH
    oveq12
    adantl
    homfval.x
    homfval.y
    wph
    cX
    cY
    cH
    ovexd
    ovmpt2d
end
