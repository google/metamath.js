include "cgrp.mm"
include "wcel.mm"
include "cmnd.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "grpmnd.mm"
include "mndass.mm"
include "sylan.mm"

theorem grpass
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vm: setvar m
  let c.0: class .0.
  assume grpcl.b: |- B = ( Base ` G )
  assume grpcl.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Grp /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .+ Y ) .+ Z ) = ( X .+ ( Y .+ Z ) ) )

  proof
    cG
    cgrp
    wcel
    cG
    cmnd
    wcel
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
    cX
    cY
    c.pl
    co
    cZ
    c.pl
    co
    cX
    cY
    cZ
    c.pl
    co
    c.pl
    co
    wceq
    cG
    grpmnd
    cB
    c.pl
    cG
    cX
    cY
    cZ
    grpcl.b
    grpcl.p
    mndass
    sylan
end
