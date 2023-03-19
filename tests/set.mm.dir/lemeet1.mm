include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "meetlem.mm"
include "simplld.mm"

theorem lemeet1
  let wph: wff ph
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  assume meetval2.b: |- B = ( Base ` K )
  assume meetval2.l: |- .<_ = ( le ` K )
  assume meetval2.m: |- ./\ = ( meet ` K )
  assume meetval2.k: |- ( ph -> K e. V )
  assume meetval2.x: |- ( ph -> X e. B )
  assume meetval2.y: |- ( ph -> Y e. B )
  assume meetlem.e: |- ( ph -> <. X , Y >. e. dom ./\ )


  assert |- ( ph -> ( X ./\ Y ) .<_ X )

  proof
    wph
    cX
    cY
    c.an
    co
    #
    cX
    c.le
    wbr
    @0
    cY
    c.le
    wbr
    vz
    cv
    #
    cX
    c.le
    wbr
    @1
    cY
    c.le
    wbr
    wa
    @1
    @0
    c.le
    wbr
    wi
    vz
    cB
    wral
    wph
    vz
    cB
    cK
    c.le
    c.an
    cV
    cX
    cY
    meetval2.b
    meetval2.l
    meetval2.m
    meetval2.k
    meetval2.x
    meetval2.y
    meetlem.e
    meetlem
    simplld
end
