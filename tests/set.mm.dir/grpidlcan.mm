include "cgrp.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "grplid.mm"
include "3adant3.mm"
include "eqeq2d.mm"
include "wb.mm"
include "simp1.mm"
include "simp3.mm"
include "grpidcl.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "grprcan.mm"
include "syl13anc.mm"
include "bitr3d.mm"

theorem grpidlcan
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  assume grpidrcan.b: |- B = ( Base ` G )
  assume grpidrcan.p: |- .+ = ( +g ` G )
  assume grpidrcan.o: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Grp /\ X e. B /\ Z e. B ) -> ( ( Z .+ X ) = X <-> Z = .0. ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    wcel
    #
    cZ
    cB
    wcel
    #
    w3a
    #
    cZ
    cX
    c.pl
    co
    #
    c.0
    cX
    c.pl
    co
    #
    wceq
    #
    @4
    cX
    wceq
    cZ
    c.0
    wceq
    #
    @3
    @5
    cX
    @4
    @0
    @1
    @5
    cX
    wceq
    @2
    cB
    c.pl
    cG
    cX
    c.0
    grpidrcan.b
    grpidrcan.p
    grpidrcan.o
    grplid
    3adant3
    eqeq2d
    @3
    @0
    @2
    c.0
    cB
    wcel
    #
    @1
    @6
    @7
    wb
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp3
    @0
    @1
    @8
    @2
    cB
    cG
    c.0
    grpidrcan.b
    grpidrcan.o
    grpidcl
    3ad2ant1
    @0
    @1
    @2
    simp2
    cB
    c.pl
    cG
    cZ
    c.0
    cX
    grpidrcan.b
    grpidrcan.p
    grprcan
    syl13anc
    bitr3d
end
