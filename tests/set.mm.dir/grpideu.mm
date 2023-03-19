include "cgrp.mm"
include "wcel.mm"
include "cmnd.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wral.mm"
include "wreu.mm"
include "grpmnd.mm"
include "mndideu.mm"
include "syl.mm"

theorem grpideu
  let vx: setvar x
  let vu: setvar u
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.0: class .0.
  let vy: setvar y
  let va: setvar a
  let vm: setvar m
  let cX: class X
  assume grpcl.b: |- B = ( Base ` G )
  assume grpcl.p: |- .+ = ( +g ` G )
  assume grpinvex.p: |- .0. = ( 0g ` G )

  disjoint u x
  disjoint B u
  disjoint B x
  disjoint G u
  disjoint G x
  disjoint .+ u
  disjoint .+ x
  disjoint .0. x
  disjoint u y
  disjoint x y
  disjoint B y
  disjoint a m
  disjoint a u
  disjoint a x
  disjoint a y
  disjoint G a
  disjoint m u
  disjoint m x
  disjoint m y
  disjoint G m
  disjoint G y
  disjoint X x
  disjoint X y
  assert |- ( G e. Grp -> E! u e. B A. x e. B ( ( u .+ x ) = x /\ ( x .+ u ) = x ) )

  proof
    cG
    cgrp
    wcel
    cG
    cmnd
    wcel
    vu
    cv
    #
    vx
    cv
    #
    c.pl
    co
    @1
    wceq
    @1
    @0
    c.pl
    co
    @1
    wceq
    wa
    vx
    cB
    wral
    vu
    cB
    wreu
    cG
    grpmnd
    vx
    vu
    cB
    c.pl
    cG
    grpcl.b
    grpcl.p
    mndideu
    syl
end
