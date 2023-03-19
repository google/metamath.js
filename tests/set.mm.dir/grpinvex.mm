include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "cmnd.mm"
include "isgrp.mm"
include "simprbi.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rexbidv.mm"
include "rspccva.mm"
include "sylan.mm"

theorem grpinvex
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let c.0: class .0.
  let vu: setvar u
  let vx: setvar x
  let va: setvar a
  let vm: setvar m
  assume grpcl.b: |- B = ( Base ` G )
  assume grpcl.p: |- .+ = ( +g ` G )
  assume grpinvex.p: |- .0. = ( 0g ` G )

  disjoint B y
  disjoint G y
  disjoint X y
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint x y
  disjoint B x
  disjoint a m
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint G a
  disjoint m u
  disjoint m x
  disjoint m y
  disjoint G m
  disjoint G u
  disjoint G x
  disjoint .+ u
  disjoint .+ x
  disjoint X x
  disjoint .0. x
  assert |- ( ( G e. Grp /\ X e. B ) -> E. y e. B ( y .+ X ) = .0. )

  proof
    cG
    cgrp
    wcel
    #
    vy
    cv
    #
    vx
    cv
    #
    c.pl
    co
    #
    c.0
    wceq
    #
    vy
    cB
    wrex
    #
    vx
    cB
    wral
    #
    cX
    cB
    wcel
    @1
    cX
    c.pl
    co
    #
    c.0
    wceq
    #
    vy
    cB
    wrex
    #
    @0
    cG
    cmnd
    wcel
    @6
    cB
    c.pl
    vy
    cG
    c.0
    vx
    grpcl.b
    grpcl.p
    grpinvex.p
    isgrp
    simprbi
    @5
    @9
    vx
    cX
    cB
    @2
    cX
    wceq
    #
    @4
    @8
    vy
    cB
    @10
    @3
    @7
    c.0
    @2
    cX
    @1
    c.pl
    oveq2
    eqeq1d
    rexbidv
    rspccva
    sylan
end
