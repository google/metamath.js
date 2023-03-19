include "cv.mm"
include "cfv.mm"
include "wbr.mm"
include "wral.mm"
include "wcel.mm"
include "wi.mm"
include "lubprop.mm"
include "simpld.mm"
include "breq1.mm"
include "rspccva.mm"
include "syl2anc.mm"

theorem luble
  let wph: wff ph
  let cB: class B
  let cS: class S
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  assume lubprop.b: |- B = ( Base ` K )
  assume lubprop.l: |- .<_ = ( le ` K )
  assume lubprop.u: |- U = ( lub ` K )
  assume lubprop.k: |- ( ph -> K e. V )
  assume lubprop.s: |- ( ph -> S e. dom U )
  assume luble.x: |- ( ph -> X e. S )


  assert |- ( ph -> X .<_ ( U ` S ) )

  proof
    wph
    vy
    cv
    #
    cS
    cU
    cfv
    #
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    cX
    cS
    wcel
    cX
    @1
    c.le
    wbr
    #
    wph
    @3
    @0
    vz
    cv
    #
    c.le
    wbr
    vy
    cS
    wral
    @1
    @5
    c.le
    wbr
    wi
    vz
    cB
    wral
    wph
    vy
    vz
    cB
    cS
    cU
    cK
    c.le
    cV
    lubprop.b
    lubprop.l
    lubprop.u
    lubprop.k
    lubprop.s
    lubprop
    simpld
    luble.x
    @2
    @4
    vy
    cX
    cS
    @0
    cX
    @1
    c.le
    breq1
    rspccva
    syl2anc
end
