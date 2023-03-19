include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "c0g.mm"
include "cfv.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "grpaddsubass.mm"
include "syl13anc.mm"
include "wa.mm"
include "eqid.mm"
include "grpsubid.mm"
include "oveq2d.mm"
include "3adant2.mm"
include "grprid.mm"
include "3adant3.mm"
include "3eqtrd.mm"

theorem grppncan
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  assume grpsubadd.b: |- B = ( Base ` G )
  assume grpsubadd.p: |- .+ = ( +g ` G )
  assume grpsubadd.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Grp /\ X e. B /\ Y e. B ) -> ( ( X .+ Y ) .- Y ) = X )

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
    c.pl
    co
    cY
    c.mi
    co
    #
    cX
    cY
    cY
    c.mi
    co
    #
    c.pl
    co
    #
    cX
    cG
    c0g
    cfv
    #
    c.pl
    co
    #
    cX
    @3
    @0
    @1
    @2
    @2
    @4
    @6
    wceq
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    #
    @9
    cB
    c.pl
    cG
    c.mi
    cX
    cY
    cY
    grpsubadd.b
    grpsubadd.p
    grpsubadd.m
    grpaddsubass
    syl13anc
    @0
    @2
    @6
    @8
    wceq
    @1
    @0
    @2
    wa
    @5
    @7
    cX
    c.pl
    cB
    cG
    c.mi
    cY
    @7
    grpsubadd.b
    @7
    eqid
    #
    grpsubadd.m
    grpsubid
    oveq2d
    3adant2
    @0
    @1
    @8
    cX
    wceq
    @2
    cB
    c.pl
    cG
    cX
    @7
    grpsubadd.b
    grpsubadd.p
    @10
    grprid
    3adant3
    3eqtrd
end
