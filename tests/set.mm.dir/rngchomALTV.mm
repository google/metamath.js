include "cv.mm"
include "crngh.mm"
include "co.mm"
include "cvv.mm"
include "rngchomfvalALTV.mm"
include "wceq.mm"
include "wa.mm"
include "oveq12.mm"
include "adantl.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem rngchomALTV
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vz: setvar z
  let vk: setvar k
  assume rngcbasALTV.c: |- C = ( RngCatALTV ` U )
  assume rngcbasALTV.b: |- B = ( Base ` C )
  assume rngcbasALTV.u: |- ( ph -> U e. V )
  assume rngchomfvalALTV.h: |- H = ( Hom ` C )
  assume rngchomALTV.x: |- ( ph -> X e. B )
  assume rngchomALTV.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X H Y ) = ( X RngHomo Y ) )

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
    crngh
    co
    #
    cX
    cY
    crngh
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
    rngcbasALTV.c
    rngcbasALTV.b
    rngcbasALTV.u
    rngchomfvalALTV.h
    rngchomfvalALTV
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
    crngh
    oveq12
    adantl
    rngchomALTV.x
    rngchomALTV.y
    wph
    cX
    cY
    crngh
    ovexd
    ovmpt2d
end
