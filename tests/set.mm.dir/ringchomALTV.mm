include "cv.mm"
include "crh.mm"
include "co.mm"
include "cvv.mm"
include "ringchomfvalALTV.mm"
include "wceq.mm"
include "wa.mm"
include "oveq12.mm"
include "adantl.mm"
include "ovexd.mm"
include "ovmpt2d.mm"

theorem ringchomALTV
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
  assume ringcbasALTV.c: |- C = ( RingCatALTV ` U )
  assume ringcbasALTV.b: |- B = ( Base ` C )
  assume ringcbasALTV.u: |- ( ph -> U e. V )
  assume ringchomfvalALTV.h: |- H = ( Hom ` C )
  assume ringchomALTV.x: |- ( ph -> X e. B )
  assume ringchomALTV.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X H Y ) = ( X RingHom Y ) )

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
    crh
    co
    #
    cX
    cY
    crh
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
    ringcbasALTV.c
    ringcbasALTV.b
    ringcbasALTV.u
    ringchomfvalALTV.h
    ringchomfvalALTV
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
    crh
    oveq12
    adantl
    ringchomALTV.x
    ringchomALTV.y
    wph
    cX
    cY
    crh
    ovexd
    ovmpt2d
end
