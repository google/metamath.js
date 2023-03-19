include "co.mm"
include "wcel.mm"
include "crngh.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "rngchom.mm"
include "eleq2d.mm"
include "eqid.mm"
include "rnghmf.mm"
include "syl6bi.mm"

theorem elrngchom
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
  assume rngcbas.c: |- C = ( RngCat ` U )
  assume rngcbas.b: |- B = ( Base ` C )
  assume rngcbas.u: |- ( ph -> U e. V )
  assume rngchomfval.h: |- H = ( Hom ` C )
  assume rngchom.x: |- ( ph -> X e. B )
  assume rngchom.y: |- ( ph -> Y e. B )


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
    crngh
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
    rngcbas.c
    rngcbas.b
    rngcbas.u
    rngchomfval.h
    rngchom.x
    rngchom.y
    rngchom
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
    rnghmf
    syl6bi
end
