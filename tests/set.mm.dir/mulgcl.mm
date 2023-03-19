include "cgrp.mm"
include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "cminusg.mm"
include "c0g.mm"
include "eqid.mm"
include "id.mm"
include "wss.mm"
include "ssid.mm"
include "a1i.mm"
include "cv.mm"
include "grpcl.mm"
include "grpidcl.mm"
include "grpinvcl.mm"
include "mulgsubcl.mm"

theorem mulgcl
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume mulgnncl.b: |- B = ( Base ` G )
  assume mulgnncl.t: |- .x. = ( .g ` G )


  assert |- ( ( G e. Grp /\ N e. ZZ /\ X e. B ) -> ( N .x. X ) e. B )

  proof
    cG
    cgrp
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
    cG
    cminusg
    cfv
    #
    cN
    cgrp
    cX
    cG
    c0g
    cfv
    #
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
    @1
    cG
    vx
    cv
    #
    vy
    cv
    mulgnncl.b
    @4
    grpcl
    @3
    eqid
    #
    cB
    cG
    @3
    mulgnncl.b
    @6
    grpidcl
    @2
    eqid
    #
    cB
    cG
    @2
    @5
    mulgnncl.b
    @7
    grpinvcl
    mulgsubcl
end
