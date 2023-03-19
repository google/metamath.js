include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "wreu.mm"
include "grpinvex.mm"
include "w3a.mm"
include "eqtr3.mm"
include "grprcan.mm"
include "syl5ib.mm"
include "3exp2.mm"
include "com24.mm"
include "imp41.mm"
include "an32s.mm"
include "expd.mm"
include "ralrimdva.mm"
include "ancld.mm"
include "reximdva.mm"
include "mpd.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "reu8.mm"
include "sylibr.mm"

theorem grpinveu
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let c.0: class .0.
  let vz: setvar z
  assume grpinveu.b: |- B = ( Base ` G )
  assume grpinveu.p: |- .+ = ( +g ` G )
  assume grpinveu.o: |- .0. = ( 0g ` G )

  disjoint B y
  disjoint G y
  disjoint .+ y
  disjoint .0. y
  disjoint X y
  disjoint y z
  disjoint B z
  disjoint G z
  disjoint .+ z
  disjoint .0. z
  disjoint X z
  assert |- ( ( G e. Grp /\ X e. B ) -> E! y e. B ( y .+ X ) = .0. )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    vy
    cv
    #
    cX
    c.pl
    co
    #
    c.0
    wceq
    #
    vz
    cv
    #
    cX
    c.pl
    co
    #
    c.0
    wceq
    #
    @3
    @6
    wceq
    #
    wi
    #
    vz
    cB
    wral
    #
    wa
    #
    vy
    cB
    wrex
    #
    @5
    vy
    cB
    wreu
    @2
    @5
    vy
    cB
    wrex
    @13
    vy
    cB
    c.pl
    cG
    cX
    c.0
    grpinveu.b
    grpinveu.p
    grpinveu.o
    grpinvex
    @2
    @5
    @12
    vy
    cB
    @2
    @3
    cB
    wcel
    #
    wa
    #
    @5
    @11
    @15
    @5
    @10
    vz
    cB
    @15
    @6
    cB
    wcel
    #
    wa
    @5
    @8
    @9
    @2
    @16
    @14
    @5
    @8
    wa
    #
    @9
    wi
    #
    @0
    @1
    @16
    @14
    @18
    @0
    @14
    @16
    @1
    @18
    @0
    @14
    @16
    @1
    @18
    @17
    @4
    @7
    wceq
    @0
    @14
    @16
    @1
    w3a
    wa
    @9
    @4
    @7
    c.0
    eqtr3
    cB
    c.pl
    cG
    @3
    @6
    cX
    grpinveu.b
    grpinveu.p
    grprcan
    syl5ib
    3exp2
    com24
    imp41
    an32s
    expd
    ralrimdva
    ancld
    reximdva
    mpd
    @5
    @8
    vy
    vz
    cB
    @9
    @4
    @7
    c.0
    @3
    @6
    cX
    c.pl
    oveq1
    eqeq1d
    reu8
    sylibr
end
