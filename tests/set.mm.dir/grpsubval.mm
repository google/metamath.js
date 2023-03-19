include "cv.mm"
include "cfv.mm"
include "co.mm"
include "oveq1.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "grpsubfval.mm"
include "ovex.mm"
include "ovmpt2.mm"

theorem grpsubval
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cI: class I
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  assume grpsubval.b: |- B = ( Base ` G )
  assume grpsubval.p: |- .+ = ( +g ` G )
  assume grpsubval.i: |- I = ( invg ` G )
  assume grpsubval.m: |- .- = ( -g ` G )


  assert |- ( ( X e. B /\ Y e. B ) -> ( X .- Y ) = ( X .+ ( I ` Y ) ) )

  proof
    vx
    vy
    cX
    cY
    cB
    cB
    vx
    cv
    #
    vy
    cv
    #
    cI
    cfv
    #
    c.pl
    co
    cX
    cY
    cI
    cfv
    #
    c.pl
    co
    c.mi
    cX
    @2
    c.pl
    co
    @0
    cX
    @2
    c.pl
    oveq1
    @1
    cY
    wceq
    @2
    @3
    cX
    c.pl
    @1
    cY
    cI
    fveq2
    oveq2d
    vx
    vy
    cB
    c.pl
    cG
    cI
    c.mi
    grpsubval.b
    grpsubval.p
    grpsubval.i
    grpsubval.m
    grpsubfval
    cX
    @3
    c.pl
    ovex
    ovmpt2
end
