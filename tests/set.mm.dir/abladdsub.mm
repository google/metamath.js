include "cabl.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "ablcom.mm"
include "3adant3r3.mm"
include "oveq1d.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "adantr.mm"
include "simpr2.mm"
include "simpr1.mm"
include "simpr3.mm"
include "grpaddsubass.mm"
include "syl13anc.mm"
include "simpl.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "3eqtrd.mm"

theorem abladdsub
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume ablsubadd.b: |- B = ( Base ` G )
  assume ablsubadd.p: |- .+ = ( +g ` G )
  assume ablsubadd.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Abel /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .+ Y ) .- Z ) = ( ( X .- Z ) .+ Y ) )

  proof
    cG
    cabl
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
    c.mi
    co
    cY
    cX
    c.pl
    co
    #
    cZ
    c.mi
    co
    #
    cY
    cX
    cZ
    c.mi
    co
    #
    c.pl
    co
    #
    @9
    cY
    c.pl
    co
    #
    @5
    @6
    @7
    cZ
    c.mi
    @0
    @1
    @2
    @6
    @7
    wceq
    @3
    cB
    c.pl
    cG
    cX
    cY
    ablsubadd.b
    ablsubadd.p
    ablcom
    3adant3r3
    oveq1d
    @5
    cG
    cgrp
    wcel
    #
    @2
    @1
    @3
    @8
    @10
    wceq
    @0
    @12
    @4
    cG
    ablgrp
    adantr
    #
    @0
    @1
    @2
    @3
    simpr2
    #
    @0
    @1
    @2
    @3
    simpr1
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
    cY
    cX
    cZ
    ablsubadd.b
    ablsubadd.p
    ablsubadd.m
    grpaddsubass
    syl13anc
    @5
    @0
    @2
    @9
    cB
    wcel
    #
    @10
    @11
    wceq
    @0
    @4
    simpl
    @14
    @5
    @12
    @1
    @3
    @17
    @13
    @15
    @16
    cB
    cG
    c.mi
    cX
    cZ
    ablsubadd.b
    ablsubadd.m
    grpsubcl
    syl3anc
    cB
    c.pl
    cG
    cY
    @9
    ablsubadd.b
    ablsubadd.p
    ablcom
    syl3anc
    3eqtrd
end
