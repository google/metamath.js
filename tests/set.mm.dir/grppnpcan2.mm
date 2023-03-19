include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "grpcl.mm"
include "3adant3r2.mm"
include "simpr3.mm"
include "simpr2.mm"
include "grpsubsub4.mm"
include "syl13anc.mm"
include "grppncan.mm"
include "oveq1d.mm"
include "eqtr3d.mm"

theorem grppnpcan2
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


  assert |- ( ( G e. Grp /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .+ Z ) .- ( Y .+ Z ) ) = ( X .- Y ) )

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
    cZ
    c.pl
    co
    #
    cZ
    c.mi
    co
    #
    cY
    c.mi
    co
    #
    @6
    cY
    cZ
    c.pl
    co
    c.mi
    co
    #
    cX
    cY
    c.mi
    co
    @5
    @0
    @6
    cB
    wcel
    #
    @3
    @2
    @8
    @9
    wceq
    @0
    @4
    simpl
    @0
    @1
    @3
    @10
    @2
    cB
    c.pl
    cG
    cX
    cZ
    grpsubadd.b
    grpsubadd.p
    grpcl
    3adant3r2
    @0
    @1
    @2
    @3
    simpr3
    @0
    @1
    @2
    @3
    simpr2
    cB
    c.pl
    cG
    c.mi
    @6
    cZ
    cY
    grpsubadd.b
    grpsubadd.p
    grpsubadd.m
    grpsubsub4
    syl13anc
    @5
    @7
    cX
    cY
    c.mi
    @0
    @1
    @3
    @7
    cX
    wceq
    @2
    cB
    c.pl
    cG
    c.mi
    cX
    cZ
    grpsubadd.b
    grpsubadd.p
    grpsubadd.m
    grppncan
    3adant3r2
    oveq1d
    eqtr3d
end
