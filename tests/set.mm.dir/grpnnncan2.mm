include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "simpl.mm"
include "simpr1.mm"
include "simpr3.mm"
include "grpsubcl.mm"
include "3adant3r1.mm"
include "eqid.mm"
include "grpsubsub4.mm"
include "syl13anc.mm"
include "grpnpcan.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem grpnnncan2
  let cB: class B
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume grpnnncan2.b: |- B = ( Base ` G )
  assume grpnnncan2.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Grp /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .- Z ) .- ( Y .- Z ) ) = ( X .- Y ) )

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
    c.mi
    co
    cY
    cZ
    c.mi
    co
    #
    c.mi
    co
    #
    cX
    @6
    cZ
    cG
    cplusg
    cfv
    #
    co
    #
    c.mi
    co
    #
    cX
    cY
    c.mi
    co
    @5
    @0
    @1
    @3
    @6
    cB
    wcel
    #
    @7
    @10
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
    simpr3
    @0
    @2
    @3
    @11
    @1
    cB
    cG
    c.mi
    cY
    cZ
    grpnnncan2.b
    grpnnncan2.m
    grpsubcl
    3adant3r1
    cB
    @8
    cG
    c.mi
    cX
    cZ
    @6
    grpnnncan2.b
    @8
    eqid
    #
    grpnnncan2.m
    grpsubsub4
    syl13anc
    @5
    @9
    cY
    cX
    c.mi
    @0
    @2
    @3
    @9
    cY
    wceq
    @1
    cB
    @8
    cG
    c.mi
    cY
    cZ
    grpnnncan2.b
    @12
    grpnnncan2.m
    grpnpcan
    3adant3r1
    oveq2d
    eqtrd
end
