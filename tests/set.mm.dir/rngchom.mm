include "co.mm"
include "crngh.mm"
include "cxp.mm"
include "cres.mm"
include "rngchomfval.mm"
include "oveqd.mm"
include "ovresd.mm"
include "eqtrd.mm"

theorem rngchom
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
  assume rngcbas.c: |- C = ( RngCat ` U )
  assume rngcbas.b: |- B = ( Base ` C )
  assume rngcbas.u: |- ( ph -> U e. V )
  assume rngchomfval.h: |- H = ( Hom ` C )
  assume rngchom.x: |- ( ph -> X e. B )
  assume rngchom.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X H Y ) = ( X RngHomo Y ) )

  proof
    wph
    cX
    cY
    cH
    co
    cX
    cY
    crngh
    cB
    cB
    cxp
    cres
    #
    co
    cX
    cY
    crngh
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
    rngcbas.c
    rngcbas.b
    rngcbas.u
    rngchomfval.h
    rngchomfval
    oveqd
    wph
    cX
    cY
    crngh
    cB
    rngchom.x
    rngchom.y
    ovresd
    eqtrd
end
