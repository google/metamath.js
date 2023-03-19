include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cminusg.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr2.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "3ad2antr3.mm"
include "grpass.mm"
include "syl13anc.mm"
include "grpcl.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem grpaddsubass
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


  assert |- ( ( G e. Grp /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .+ Y ) .- Z ) = ( X .+ ( Y .- Z ) ) )

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
    c.pl
    co
    #
    cZ
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
    cY
    @8
    c.pl
    co
    #
    c.pl
    co
    #
    @6
    cZ
    c.mi
    co
    #
    cX
    cY
    cZ
    c.mi
    co
    #
    c.pl
    co
    @5
    @0
    @1
    @2
    @8
    cB
    wcel
    #
    @9
    @11
    wceq
    @0
    @4
    simpl
    @0
    @1
    @2
    @3
    simpr1
    @0
    @1
    @2
    @3
    simpr2
    #
    @0
    @1
    @3
    @14
    @2
    cB
    cG
    @7
    cZ
    grpsubadd.b
    @7
    eqid
    #
    grpinvcl
    3ad2antr3
    cB
    c.pl
    cG
    cX
    cY
    @8
    grpsubadd.b
    grpsubadd.p
    grpass
    syl13anc
    @5
    @6
    cB
    wcel
    #
    @3
    @12
    @9
    wceq
    @0
    @1
    @2
    @17
    @3
    cB
    c.pl
    cG
    cX
    cY
    grpsubadd.b
    grpsubadd.p
    grpcl
    3adant3r3
    @0
    @1
    @2
    @3
    simpr3
    #
    cB
    c.pl
    cG
    @7
    c.mi
    @6
    cZ
    grpsubadd.b
    grpsubadd.p
    @16
    grpsubadd.m
    grpsubval
    syl2anc
    @5
    @13
    @10
    cX
    c.pl
    @5
    @2
    @3
    @13
    @10
    wceq
    @15
    @18
    cB
    c.pl
    cG
    @7
    c.mi
    cY
    cZ
    grpsubadd.b
    grpsubadd.p
    @16
    grpsubadd.m
    grpsubval
    syl2anc
    oveq2d
    3eqtr4d
end
