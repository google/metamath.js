include "cabl.mm"
include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cgrp.mm"
include "wb.mm"
include "ablgrp.mm"
include "grpsubadd.mm"
include "sylan.mm"
include "ablcom.mm"
include "3adant3r1.mm"
include "eqeq1d.mm"
include "bitr4d.mm"

theorem ablsubadd
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


  assert |- ( ( G e. Abel /\ ( X e. B /\ Y e. B /\ Z e. B ) ) -> ( ( X .- Y ) = Z <-> ( Y .+ Z ) = X ) )

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
    c.mi
    co
    cZ
    wceq
    #
    cZ
    cY
    c.pl
    co
    #
    cX
    wceq
    #
    cY
    cZ
    c.pl
    co
    #
    cX
    wceq
    @0
    cG
    cgrp
    wcel
    @4
    @6
    @8
    wb
    cG
    ablgrp
    cB
    c.pl
    cG
    c.mi
    cX
    cY
    cZ
    ablsubadd.b
    ablsubadd.p
    ablsubadd.m
    grpsubadd
    sylan
    @5
    @9
    @7
    cX
    @0
    @2
    @3
    @9
    @7
    wceq
    @1
    cB
    c.pl
    cG
    cY
    cZ
    ablsubadd.b
    ablsubadd.p
    ablcom
    3adant3r1
    eqeq1d
    bitr4d
end
