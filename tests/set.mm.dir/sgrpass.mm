include "csgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "cmgm.mm"
include "cv.mm"
include "wral.mm"
include "wi.mm"
include "issgrp.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "rspc3v.mm"
include "com12.mm"
include "simplbiim.mm"
include "imp.mm"

theorem sgrpass
  let cB: class B
  let cG: class G
  let cX: class X
  let cY: class Y
  let c.op: class .o.
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume sgrpass.b: |- B = ( Base ` G )
  assume sgrpass.o: |- .o. = ( +g ` G )


  assert |- ( ( G e. SGrp /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .o. Y ) .o. Z ) = ( X .o. ( Y .o. Z ) ) )

  proof
    cG
    csgrp
    wcel
    #
    cX
    cB
    wcel
    cY
    cB
    wcel
    cZ
    cB
    wcel
    w3a
    #
    cX
    cY
    c.op
    co
    #
    cZ
    c.op
    co
    #
    cX
    cY
    cZ
    c.op
    co
    #
    c.op
    co
    #
    wceq
    #
    @0
    cG
    cmgm
    wcel
    vx
    cv
    #
    vy
    cv
    #
    c.op
    co
    #
    vz
    cv
    #
    c.op
    co
    #
    @7
    @8
    @10
    c.op
    co
    #
    c.op
    co
    #
    wceq
    #
    vz
    cB
    wral
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @1
    @6
    wi
    vx
    vy
    vz
    cB
    cG
    c.op
    sgrpass.b
    sgrpass.o
    issgrp
    @1
    @15
    @6
    @14
    @6
    cX
    @8
    c.op
    co
    #
    @10
    c.op
    co
    #
    cX
    @12
    c.op
    co
    #
    wceq
    @2
    @10
    c.op
    co
    #
    cX
    cY
    @10
    c.op
    co
    #
    c.op
    co
    #
    wceq
    vx
    vy
    vz
    cX
    cY
    cZ
    cB
    cB
    cB
    @7
    cX
    wceq
    #
    @11
    @17
    @13
    @18
    @22
    @9
    @16
    @10
    c.op
    @7
    cX
    @8
    c.op
    oveq1
    oveq1d
    @7
    cX
    @12
    c.op
    oveq1
    eqeq12d
    @8
    cY
    wceq
    #
    @17
    @19
    @18
    @21
    @23
    @16
    @2
    @10
    c.op
    @8
    cY
    cX
    c.op
    oveq2
    oveq1d
    @23
    @12
    @20
    cX
    c.op
    @8
    cY
    @10
    c.op
    oveq1
    oveq2d
    eqeq12d
    @10
    cZ
    wceq
    #
    @19
    @3
    @21
    @5
    @10
    cZ
    @2
    c.op
    oveq2
    @24
    @20
    @4
    cX
    c.op
    @10
    cZ
    cY
    c.op
    oveq2
    oveq2d
    eqeq12d
    rspc3v
    com12
    simplbiim
    imp
end
