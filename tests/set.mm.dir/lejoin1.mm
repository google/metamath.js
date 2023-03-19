include "co.mm"
include "wbr.mm"
include "cv.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "joinlem.mm"
include "simplld.mm"

theorem lejoin1
  let wph: wff ph
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  assume joinval2.b: |- B = ( Base ` K )
  assume joinval2.l: |- .<_ = ( le ` K )
  assume joinval2.j: |- .\/ = ( join ` K )
  assume joinval2.k: |- ( ph -> K e. V )
  assume joinval2.x: |- ( ph -> X e. B )
  assume joinval2.y: |- ( ph -> Y e. B )
  assume joinlem.e: |- ( ph -> <. X , Y >. e. dom .\/ )


  assert |- ( ph -> X .<_ ( X .\/ Y ) )

  proof
    wph
    cX
    cX
    cY
    c.or
    co
    #
    c.le
    wbr
    cY
    @0
    c.le
    wbr
    cX
    vz
    cv
    #
    c.le
    wbr
    cY
    @1
    c.le
    wbr
    wa
    @0
    @1
    c.le
    wbr
    wi
    vz
    cB
    wral
    wph
    vz
    cB
    c.or
    cK
    c.le
    cV
    cX
    cY
    joinval2.b
    joinval2.l
    joinval2.j
    joinval2.k
    joinval2.x
    joinval2.y
    joinlem.e
    joinlem
    simplld
end
