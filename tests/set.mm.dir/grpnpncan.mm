include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "grpsubcl.mm"
include "3adant3r3.mm"
include "simpr2.mm"
include "simpr3.mm"
include "grpaddsubass.mm"
include "syl13anc.mm"
include "grpnpcan.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem grpnpncan
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume grpsubadd.b: |- B = ( Base ` G )
  assume grpsubadd.p: |- .+ = ( +g ` G )
  assume grpsubadd.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Grp /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .- Y ) .+ ( Y .- Z ) ) = ( X .- Z ) )

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
    cZ
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cX
    cY
    c.mi
    co
    #
    cY
    c.pl
    co
    #
    cZ
    c.mi
    co
    #
    @6
    cY
    cZ
    c.mi
    co
    c.pl
    co
    #
    cX
    cZ
    c.mi
    co
    @5
    @0
    @6
    cB
    wcel
    #
    @2
    @3
    @8
    @9
    wceq
    @0
    @4
    simpl
    @0
    @1
    @2
    @10
    @3
    cB
    cG
    c.mi
    cX
    cY
    grpsubadd.b
    grpsubadd.m
    grpsubcl
    3adant3r3
    @0
    @1
    @2
    @3
    simpr2
    @0
    @1
    @2
    @3
    simpr3
    cB
    c.pl
    cG
    c.mi
    @6
    cY
    cZ
    grpsubadd.b
    grpsubadd.p
    grpsubadd.m
    grpaddsubass
    syl13anc
    @5
    @7
    cX
    cZ
    c.mi
    @0
    @1
    @2
    @7
    cX
    wceq
    @3
    cB
    c.pl
    cG
    c.mi
    cX
    cY
    grpsubadd.b
    grpsubadd.p
    grpsubadd.m
    grpnpcan
    3adant3r3
    oveq1d
    eqtr3d
end
