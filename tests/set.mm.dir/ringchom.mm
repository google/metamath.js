include "co.mm"
include "crh.mm"
include "cxp.mm"
include "cres.mm"
include "ringchomfval.mm"
include "oveqd.mm"
include "ovresd.mm"
include "eqtrd.mm"

theorem ringchom
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cH: class H
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume ringcbas.c: |- C = ( RingCat ` U )
  assume ringcbas.b: |- B = ( Base ` C )
  assume ringcbas.u: |- ( ph -> U e. V )
  assume ringchomfval.h: |- H = ( Hom ` C )
  assume ringchom.x: |- ( ph -> X e. B )
  assume ringchom.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X H Y ) = ( X RingHom Y ) )

  proof
    wph
    cX
    cY
    cH
    co
    cX
    cY
    crh
    cB
    cB
    cxp
    cres
    #
    co
    cX
    cY
    crh
    co
    wph
    cH
    @0
    cX
    cY
    wph
    cB
    cC
    cU
    cH
    cV
    ringcbas.c
    ringcbas.b
    ringcbas.u
    ringchomfval.h
    ringchomfval
    oveqd
    wph
    cX
    cY
    crh
    cB
    ringchom.x
    ringchom.y
    ovresd
    eqtrd
end
