include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "grpsubcl.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "grpnpcan.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "simpr2.mm"
include "grpass.mm"
include "syl13anc.mm"
include "3eqtr3d.mm"
include "wb.mm"
include "simpr1.mm"
include "grpcl.mm"
include "grpsubadd.mm"
include "mpbird.mm"
include "eqcomd.mm"

theorem grpsubsub4
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


  assert |- ( ( G e. Grp /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .- Y ) .- Z ) = ( X .- ( Z .+ Y ) ) )

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
    cY
    c.pl
    co
    #
    c.mi
    co
    #
    cX
    cY
    c.mi
    co
    #
    cZ
    c.mi
    co
    #
    @5
    @7
    @9
    wceq
    #
    @9
    @6
    c.pl
    co
    #
    cX
    wceq
    #
    @5
    @9
    cZ
    c.pl
    co
    #
    cY
    c.pl
    co
    #
    @8
    cY
    c.pl
    co
    #
    @11
    cX
    @5
    @13
    @8
    cY
    c.pl
    @5
    @0
    @8
    cB
    wcel
    #
    @3
    @13
    @8
    wceq
    @0
    @4
    simpl
    #
    @0
    @1
    @2
    @16
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
    #
    @0
    @1
    @2
    @3
    simpr3
    #
    cB
    c.pl
    cG
    c.mi
    @8
    cZ
    grpsubadd.b
    grpsubadd.p
    grpsubadd.m
    grpnpcan
    syl3anc
    oveq1d
    @5
    @0
    @9
    cB
    wcel
    #
    @3
    @2
    @14
    @11
    wceq
    @17
    @5
    @0
    @16
    @3
    @20
    @17
    @18
    @19
    cB
    cG
    c.mi
    @8
    cZ
    grpsubadd.b
    grpsubadd.m
    grpsubcl
    syl3anc
    #
    @19
    @0
    @1
    @2
    @3
    simpr2
    #
    cB
    c.pl
    cG
    @9
    cZ
    cY
    grpsubadd.b
    grpsubadd.p
    grpass
    syl13anc
    @0
    @1
    @2
    @15
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
    3eqtr3d
    @5
    @0
    @1
    @6
    cB
    wcel
    #
    @20
    @10
    @12
    wb
    @17
    @0
    @1
    @2
    @3
    simpr1
    @5
    @0
    @3
    @2
    @23
    @17
    @19
    @22
    cB
    c.pl
    cG
    cZ
    cY
    grpsubadd.b
    grpsubadd.p
    grpcl
    syl3anc
    @21
    cB
    c.pl
    cG
    c.mi
    cX
    @6
    @9
    grpsubadd.b
    grpsubadd.p
    grpsubadd.m
    grpsubadd
    syl13anc
    mpbird
    eqcomd
end
