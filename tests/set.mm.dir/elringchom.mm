include "co.mm"
include "wcel.mm"
include "crh.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "ringchom.mm"
include "eleq2d.mm"
include "eqid.mm"
include "rhmf.mm"
include "syl6bi.mm"

theorem elringchom
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
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


  assert |- ( ph -> ( F e. ( X H Y ) -> F : ( Base ` X ) --> ( Base ` Y ) ) )

  proof
    wph
    cF
    cX
    cY
    cH
    co
    #
    wcel
    cF
    cX
    cY
    crh
    co
    #
    wcel
    cX
    cbs
    cfv
    #
    cY
    cbs
    cfv
    #
    cF
    wf
    wph
    @0
    @1
    cF
    wph
    cB
    cC
    cU
    cH
    cV
    cX
    cY
    ringcbas.c
    ringcbas.b
    ringcbas.u
    ringchomfval.h
    ringchom.x
    ringchom.y
    ringchom
    eleq2d
    @2
    @3
    cX
    cY
    cF
    @2
    eqid
    @3
    eqid
    rhmf
    syl6bi
end
