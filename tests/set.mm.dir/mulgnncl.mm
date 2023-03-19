include "cmgm.mm"
include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "eqid.mm"
include "id.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cv.mm"
include "mgmcl.mm"
include "mulgnnsubcl.mm"

theorem mulgnncl
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume mulgnncl.b: |- B = ( Base ` G )
  assume mulgnncl.t: |- .x. = ( .g ` G )


  assert |- ( ( G e. Mgm /\ N e. NN /\ X e. B ) -> ( N .x. X ) e. B )

  proof
    cG
    cmgm
    wcel
    #
    vx
    vy
    cB
    cG
    cplusg
    cfv
    #
    cB
    c.x
    cG
    cN
    cmgm
    cX
    mulgnncl.b
    mulgnncl.t
    @1
    eqid
    #
    @0
    id
    cB
    cB
    wss
    @0
    cB
    ssid
    a1i
    cB
    cG
    vx
    cv
    vy
    cv
    @1
    mulgnncl.b
    @2
    mgmcl
    mulgnnsubcl
end
