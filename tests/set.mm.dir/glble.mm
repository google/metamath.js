include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wcel.mm"
include "wi.mm"
include "glbprop.mm"
include "simpld.mm"
include "breq2.mm"
include "rspccva.mm"
include "syl2anc.mm"

theorem glble
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
  assume glbprop.b: |- B = ( Base ` K )
  assume glbprop.l: |- .<_ = ( le ` K )
  assume glbprop.u: |- U = ( glb ` K )
  assume glbprop.k: |- ( ph -> K e. V )
  assume glbprop.s: |- ( ph -> S e. dom U )
  assume glble.x: |- ( ph -> X e. S )


  assert |- ( ph -> ( U ` S ) .<_ X )

  proof
    wph
    cS
    cU
    cfv
    #
    vy
    cv
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
    @0
    cX
    c.le
    wbr
    #
    wph
    @3
    vz
    cv
    #
    @1
    c.le
    wbr
    vy
    cS
    wral
    @5
    @0
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
    glbprop.b
    glbprop.l
    glbprop.u
    glbprop.k
    glbprop.s
    glbprop
    simpld
    glble.x
    @2
    @4
    vy
    cX
    cS
    @1
    cX
    @0
    c.le
    breq2
    rspccva
    syl2anc
end
