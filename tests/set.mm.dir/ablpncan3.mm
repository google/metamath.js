include "cabl.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "simpl.mm"
include "simprl.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "adantr.mm"
include "simprr.mm"
include "grpsubcl.mm"
include "syl3anc.mm"
include "ablcom.mm"
include "grpnpcan.mm"
include "eqtrd.mm"

theorem ablpncan3
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  assume ablsubadd.b: |- B = ( Base ` G )
  assume ablsubadd.p: |- .+ = ( +g ` G )
  assume ablsubadd.m: |- .- = ( -g ` G )


  assert |- ( ( G e. Abel /\ ( X e. B /\ Y e. B ) ) -> ( X .+ ( Y .- X ) ) = Y )

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
    wa
    #
    wa
    #
    cX
    cY
    cX
    c.mi
    co
    #
    c.pl
    co
    #
    @5
    cX
    c.pl
    co
    #
    cY
    @4
    @0
    @1
    @5
    cB
    wcel
    #
    @6
    @7
    wceq
    @0
    @3
    simpl
    @0
    @1
    @2
    simprl
    #
    @4
    cG
    cgrp
    wcel
    #
    @2
    @1
    @8
    @0
    @10
    @3
    cG
    ablgrp
    adantr
    #
    @0
    @1
    @2
    simprr
    #
    @9
    cB
    cG
    c.mi
    cY
    cX
    ablsubadd.b
    ablsubadd.m
    grpsubcl
    syl3anc
    cB
    c.pl
    cG
    cX
    @5
    ablsubadd.b
    ablsubadd.p
    ablcom
    syl3anc
    @4
    @10
    @2
    @1
    @7
    cY
    wceq
    @11
    @12
    @9
    cB
    c.pl
    cG
    c.mi
    cY
    cX
    ablsubadd.b
    ablsubadd.p
    ablsubadd.m
    grpnpcan
    syl3anc
    eqtrd
end
