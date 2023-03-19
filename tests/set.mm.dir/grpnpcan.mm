include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "cminusg.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "3adant2.mm"
include "grpcl.mm"
include "syld3an3.mm"
include "grpsubval.mm"
include "syl2anc.mm"
include "grppncan.mm"
include "3adant1.mm"
include "eqcomd.mm"
include "grpinvinv.mm"
include "oveq12d.mm"
include "3eqtr3rd.mm"

theorem grpnpcan
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  assume grpsubadd.b: |- B = ( Base ` G )
  assume grpsubadd.p: |- .+ = ( +g ` G )
  assume grpsubadd.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Grp /\ X e. B /\ Y e. B ) -> ( ( X .- Y ) .+ Y ) = X )

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
    cG
    cminusg
    cfv
    #
    cfv
    #
    c.pl
    co
    #
    @5
    c.mi
    co
    #
    @6
    @5
    @4
    cfv
    #
    c.pl
    co
    #
    cX
    cX
    cY
    c.mi
    co
    #
    cY
    c.pl
    co
    @3
    @6
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    @7
    @9
    wceq
    @0
    @1
    @2
    @12
    @11
    @0
    @2
    @12
    @1
    cB
    cG
    @4
    cY
    grpsubadd.b
    @4
    eqid
    #
    grpinvcl
    3adant2
    #
    cB
    c.pl
    cG
    cX
    @5
    grpsubadd.b
    grpsubadd.p
    grpcl
    syld3an3
    @14
    cB
    c.pl
    cG
    @4
    c.mi
    @6
    @5
    grpsubadd.b
    grpsubadd.p
    @13
    grpsubadd.m
    grpsubval
    syl2anc
    @0
    @1
    @2
    @12
    @7
    cX
    wceq
    @14
    cB
    c.pl
    cG
    c.mi
    cX
    @5
    grpsubadd.b
    grpsubadd.p
    grpsubadd.m
    grppncan
    syld3an3
    @3
    @6
    @10
    @8
    cY
    c.pl
    @3
    @10
    @6
    @1
    @2
    @10
    @6
    wceq
    @0
    cB
    c.pl
    cG
    @4
    c.mi
    cX
    cY
    grpsubadd.b
    grpsubadd.p
    @13
    grpsubadd.m
    grpsubval
    3adant1
    eqcomd
    @0
    @2
    @8
    cY
    wceq
    @1
    cB
    cG
    @4
    cY
    grpsubadd.b
    @13
    grpinvinv
    3adant2
    oveq12d
    3eqtr3rd
end
