include "co.mm"
include "wcel.mm"
include "crh.mm"
include "cbs.mm"
include "cfv.mm"
include "wf.mm"
include "ringchomALTV.mm"
include "eleq2d.mm"
include "eqid.mm"
include "rhmf.mm"
include "syl6bi.mm"

theorem elringchomALTV
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
  assume ringcbasALTV.c: |- C = ( RingCatALTV ` U )
  assume ringcbasALTV.b: |- B = ( Base ` C )
  assume ringcbasALTV.u: |- ( ph -> U e. V )
  assume ringchomfvalALTV.h: |- H = ( Hom ` C )
  assume ringchomALTV.x: |- ( ph -> X e. B )
  assume ringchomALTV.y: |- ( ph -> Y e. B )


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
    ringcbasALTV.c
    ringcbasALTV.b
    ringcbasALTV.u
    ringchomfvalALTV.h
    ringchomALTV.x
    ringchomALTV.y
    ringchomALTV
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
