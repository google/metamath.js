include "cv.mm"
include "cmap.mm"
include "co.mm"
include "cvv.mm"
include "setchomfval.mm"
include "wceq.mm"
include "wa.mm"
include "simprr.mm"
include "simprl.mm"
include "oveq12d.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem setchom
  let wph: wff ph
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cG: class G
  let cZ: class Z
  assume setcbas.c: |- C = ( SetCat ` U )
  assume setcbas.u: |- ( ph -> U e. V )
  assume setchomfval.h: |- H = ( Hom ` C )
  assume setchom.x: |- ( ph -> X e. U )
  assume setchom.y: |- ( ph -> Y e. U )


  assert |- ( ph -> ( X H Y ) = ( Y ^m X ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cU
    cU
    vy
    cv
    #
    vx
    cv
    #
    cmap
    co
    cY
    cX
    cmap
    co
    cH
    cvv
    wph
    vx
    vy
    cC
    cU
    cH
    cV
    setcbas.c
    setcbas.u
    setchomfval.h
    setchomfval
    wph
    @1
    cX
    wceq
    #
    @0
    cY
    wceq
    #
    wa
    wa
    @0
    cY
    @1
    cX
    cmap
    wph
    @2
    @3
    simprr
    wph
    @2
    @3
    simprl
    oveq12d
    setchom.x
    setchom.y
    wph
    cY
    cX
    cmap
    ovexd
    ovmpt2d
end
