include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "grpinvcl.mm"
include "3adant2.mm"
include "eqid.mm"
include "grpinvadd.mm"
include "syld3an3.mm"
include "grpinvinv.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "grpsubval.mm"
include "3adant1.mm"
include "fveq2d.mm"
include "ancoms.mm"
include "3eqtr4d.mm"

theorem grpinvsub
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cN: class N
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume grpsubcl.b: |- B = ( Base ` G )
  assume grpsubcl.m: |- .- = ( -g ` G )
  assume grpinvsub.n: |- N = ( invg ` G )


  assert |- ( ( G e. Grp /\ X e. B /\ Y e. B ) -> ( N ` ( X .- Y ) ) = ( Y .- X ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    cN
    cfv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cN
    cfv
    #
    cY
    cX
    cN
    cfv
    #
    @5
    co
    #
    cX
    cY
    c.mi
    co
    #
    cN
    cfv
    cY
    cX
    c.mi
    co
    #
    @3
    @7
    @4
    cN
    cfv
    #
    @8
    @5
    co
    #
    @9
    @0
    @1
    @2
    @4
    cB
    wcel
    #
    @7
    @13
    wceq
    @0
    @2
    @14
    @1
    cB
    cG
    cN
    cY
    grpsubcl.b
    grpinvsub.n
    grpinvcl
    3adant2
    cB
    @5
    cG
    cN
    cX
    @4
    grpsubcl.b
    @5
    eqid
    #
    grpinvsub.n
    grpinvadd
    syld3an3
    @3
    @12
    cY
    @8
    @5
    @0
    @2
    @12
    cY
    wceq
    @1
    cB
    cG
    cN
    cY
    grpsubcl.b
    grpinvsub.n
    grpinvinv
    3adant2
    oveq1d
    eqtrd
    @3
    @10
    @6
    cN
    @1
    @2
    @10
    @6
    wceq
    @0
    cB
    @5
    cG
    cN
    c.mi
    cX
    cY
    grpsubcl.b
    @15
    grpinvsub.n
    grpsubcl.m
    grpsubval
    3adant1
    fveq2d
    @1
    @2
    @11
    @9
    wceq
    #
    @0
    @2
    @1
    @16
    cB
    @5
    cG
    cN
    c.mi
    cY
    cX
    grpsubcl.b
    @15
    grpinvsub.n
    grpsubcl.m
    grpsubval
    ancoms
    3adant1
    3eqtr4d
end
