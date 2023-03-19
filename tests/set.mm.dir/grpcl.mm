include "cgrp.mm"
include "wcel.mm"
include "cmnd.mm"
include "co.mm"
include "grpmnd.mm"
include "mndcl.mm"
include "syl3an1.mm"

theorem grpcl
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let va: setvar a
  let vm: setvar m
  let c.0: class .0.
  assume grpcl.b: |- B = ( Base ` G )
  assume grpcl.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Grp /\ X e. B /\ Y e. B ) -> ( X .+ Y ) e. B )

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
    cX
    cY
    c.pl
    co
    cB
    wcel
    cG
    grpmnd
    cB
    c.pl
    cG
    cX
    cY
    grpcl.b
    grpcl.p
    mndcl
    syl3an1
end
