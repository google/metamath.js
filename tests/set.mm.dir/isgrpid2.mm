include "cgrp.mm"
include "wcel.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "grpid.mm"
include "biimpd.mm"
include "expimpd.mm"
include "grpidcl.mm"
include "grplid.mm"
include "mpdan.mm"
include "jca.mm"
include "eleq1.mm"
include "id.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "syl5ibcom.mm"
include "impbid.mm"

theorem isgrpid2
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.0: class .0.
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  assume grpinveu.b: |- B = ( Base ` G )
  assume grpinveu.p: |- .+ = ( +g ` G )
  assume grpinveu.o: |- .0. = ( 0g ` G )


  assert |- ( G e. Grp -> ( ( Z e. B /\ ( Z .+ Z ) = Z ) <-> .0. = Z ) )

  proof
    cG
    cgrp
    wcel
    #
    cZ
    cB
    wcel
    #
    cZ
    cZ
    c.pl
    co
    #
    cZ
    wceq
    #
    wa
    #
    c.0
    cZ
    wceq
    #
    @0
    @1
    @3
    @5
    @0
    @1
    wa
    @3
    @5
    cB
    c.pl
    cG
    cZ
    c.0
    grpinveu.b
    grpinveu.p
    grpinveu.o
    grpid
    biimpd
    expimpd
    @0
    c.0
    cB
    wcel
    #
    c.0
    c.0
    c.pl
    co
    #
    c.0
    wceq
    #
    wa
    @5
    @4
    @0
    @6
    @8
    cB
    cG
    c.0
    grpinveu.b
    grpinveu.o
    grpidcl
    #
    @0
    @6
    @8
    @9
    cB
    c.pl
    cG
    c.0
    c.0
    grpinveu.b
    grpinveu.p
    grpinveu.o
    grplid
    mpdan
    jca
    @5
    @6
    @1
    @8
    @3
    c.0
    cZ
    cB
    eleq1
    @5
    @7
    @2
    c.0
    cZ
    @5
    c.0
    cZ
    c.0
    cZ
    c.pl
    @5
    id
    #
    @10
    oveq12d
    @10
    eqeq12d
    anbi12d
    syl5ibcom
    impbid
end
