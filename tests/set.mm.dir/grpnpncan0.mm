include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "grpnpncan.mm"
include "syl13anc.mm"
include "grpsubid.mm"
include "adantrr.mm"
include "eqtrd.mm"

theorem grpnpncan0
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume grpsubadd.b: |- B = ( Base ` G )
  assume grpsubadd.p: |- .+ = ( +g ` G )
  assume grpsubadd.m: |- .- = ( -g ` G )
  assume grpnpncan0.0: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Grp /\ ( X e. B /\ Y e. B ) ) -> ( ( X .- Y ) .+ ( Y .- X ) ) = .0. )

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
    wa
    #
    wa
    #
    cX
    cY
    c.mi
    co
    cY
    cX
    c.mi
    co
    c.pl
    co
    #
    cX
    cX
    c.mi
    co
    #
    c.0
    @4
    @0
    @1
    @2
    @1
    @5
    @6
    wceq
    @0
    @3
    simpl
    @0
    @1
    @2
    simprl
    #
    @0
    @1
    @2
    simprr
    @7
    cB
    c.pl
    cG
    c.mi
    cX
    cY
    cX
    grpsubadd.b
    grpsubadd.p
    grpsubadd.m
    grpnpncan
    syl13anc
    @0
    @1
    @6
    c.0
    wceq
    @2
    cB
    cG
    c.mi
    cX
    c.0
    grpsubadd.b
    grpnpncan0.0
    grpsubadd.m
    grpsubid
    adantrr
    eqtrd
end
