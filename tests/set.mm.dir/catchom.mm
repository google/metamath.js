include "cv.mm"
include "cfunc.mm"
include "co.mm"
include "cvv.mm"
include "catchomfval.mm"
include "wceq.mm"
include "wa.mm"
include "oveq12.mm"
include "adantl.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem catchom
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let cX: class X
  let cY: class Y
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cZ: class Z
  assume catcbas.c: |- C = ( CatCat ` U )
  assume catcbas.b: |- B = ( Base ` C )
  assume catcbas.u: |- ( ph -> U e. V )
  assume catchomfval.h: |- H = ( Hom ` C )
  assume catchom.x: |- ( ph -> X e. B )
  assume catchom.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X H Y ) = ( X Func Y ) )

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
    cfunc
    co
    #
    cX
    cY
    cfunc
    co
    #
    cH
    cvv
    wph
    vx
    vy
    cB
    cC
    cU
    cH
    cV
    catcbas.c
    catcbas.b
    catcbas.u
    catchomfval.h
    catchomfval
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
    cfunc
    oveq12
    adantl
    catchom.x
    catchom.y
    wph
    cX
    cY
    cfunc
    ovexd
    ovmpt2d
end
