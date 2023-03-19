include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "cplusg.mm"
include "wceq.mm"
include "grpidcl.mm"
include "eqid.mm"
include "grpsubval.mm"
include "sylan.mm"
include "grpinvcl.mm"
include "grplid.mm"
include "syldan.mm"
include "eqtr2d.mm"

theorem grpinvval2
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume grpsubcl.b: |- B = ( Base ` G )
  assume grpsubcl.m: |- .- = ( -g ` G )
  assume grpinvsub.n: |- N = ( invg ` G )
  assume grpinvval2.z: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Grp /\ X e. B ) -> ( N ` X ) = ( .0. .- X ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    c.0
    cX
    c.mi
    co
    #
    c.0
    cX
    cN
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @3
    @0
    c.0
    cB
    wcel
    @1
    @2
    @5
    wceq
    cB
    cG
    c.0
    grpsubcl.b
    grpinvval2.z
    grpidcl
    cB
    @4
    cG
    cN
    c.mi
    c.0
    cX
    grpsubcl.b
    @4
    eqid
    #
    grpinvsub.n
    grpsubcl.m
    grpsubval
    sylan
    @0
    @1
    @3
    cB
    wcel
    @5
    @3
    wceq
    cB
    cG
    cN
    cX
    grpsubcl.b
    grpinvsub.n
    grpinvcl
    cB
    @4
    cG
    @3
    c.0
    grpsubcl.b
    @6
    grpinvval2.z
    grplid
    syldan
    eqtr2d
end
