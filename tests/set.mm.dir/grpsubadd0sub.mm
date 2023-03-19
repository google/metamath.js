include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cminusg.mm"
include "cfv.mm"
include "wceq.mm"
include "eqid.mm"
include "grpsubval.mm"
include "3adant1.mm"
include "grpinvval2.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem grpsubadd0sub
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume grpsubid.b: |- B = ( Base ` G )
  assume grpsubid.o: |- .0. = ( 0g ` G )
  assume grpsubid.m: |- .- = ( -g ` G )
  assume grpsubadd0sub.p: |- .+ = ( +g ` G )


  assert |- ( ( G e. Grp /\ X e. B /\ Y e. B ) -> ( X .- Y ) = ( X .+ ( .0. .- Y ) ) )

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
    c.mi
    co
    #
    cX
    cY
    cG
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    cX
    c.0
    cY
    c.mi
    co
    #
    c.pl
    co
    @1
    @2
    @4
    @7
    wceq
    @0
    cB
    c.pl
    cG
    @5
    c.mi
    cX
    cY
    grpsubid.b
    grpsubadd0sub.p
    @5
    eqid
    #
    grpsubid.m
    grpsubval
    3adant1
    @3
    @6
    @8
    cX
    c.pl
    @0
    @2
    @6
    @8
    wceq
    @1
    cB
    cG
    c.mi
    @5
    cY
    c.0
    grpsubid.b
    grpsubid.m
    @9
    grpsubid.o
    grpinvval2
    3adant2
    oveq2d
    eqtrd
end
