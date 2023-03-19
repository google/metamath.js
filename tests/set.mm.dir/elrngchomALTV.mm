include "co.mm"
include "wcel.mm"
include "crngh.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "rngchomALTV.mm"
include "eleq2d.mm"
include "eqid.mm"
include "rnghmf.mm"
include "syl6bi.mm"

theorem elrngchomALTV
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
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
    rngcbasALTV.c
    rngcbasALTV.b
    rngcbasALTV.u
    rngchomfvalALTV.h
    rngchomALTV.x
    rngchomALTV.y
    rngchomALTV
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
