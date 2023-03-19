include "wbr.mm"
include "wcel.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "dvdsr.mm"
include "simplbi.mm"

theorem dvdsrcl
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let vz: setvar z
  let cZ: class Z
  let c.x: class .x.
  assume dvdsr.1: |- B = ( Base ` R )
  assume dvdsr.2: |- .|| = ( ||r ` R )


  assert |- ( X .|| Y -> X e. B )

  proof
    cX
    cY
    c.pa
    wbr
    cX
    cB
    wcel
    vx
    cv
    cX
    cR
    cmulr
    cfv
    #
    co
    cY
    wceq
    vx
    cB
    wrex
    vx
    cB
    c.pa
    cR
    @0
    cX
    cY
    dvdsr.1
    dvdsr.2
    @0
    eqid
    dvdsr
    simplbi
end
