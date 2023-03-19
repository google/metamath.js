include "wceq.mm"
include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "eqcom.mm"
include "wb.mm"
include "wi.mm"
include "grpidcl.mm"
include "grprcan.mm"
include "3exp2.mm"
include "mpid.mm"
include "pm2.43d.mm"
include "imp.mm"
include "grplid.mm"
include "eqeq2d.mm"
include "bitr3d.mm"
include "syl5rbb.mm"

theorem grpid
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cX: class X
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  assume grpinveu.b: |- B = ( Base ` G )
  assume grpinveu.p: |- .+ = ( +g ` G )
  assume grpinveu.o: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Grp /\ X e. B ) -> ( ( X .+ X ) = X <-> .0. = X ) )

  proof
    c.0
    cX
    wceq
    cX
    c.0
    wceq
    #
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
    cX
    cX
    c.pl
    co
    #
    cX
    wceq
    #
    c.0
    cX
    eqcom
    @3
    @4
    c.0
    cX
    c.pl
    co
    #
    wceq
    #
    @0
    @5
    @1
    @2
    @7
    @0
    wb
    #
    @1
    @2
    @8
    @1
    @2
    c.0
    cB
    wcel
    #
    @2
    @8
    wi
    cB
    cG
    c.0
    grpinveu.b
    grpinveu.o
    grpidcl
    @1
    @2
    @9
    @2
    @8
    cB
    c.pl
    cG
    cX
    c.0
    cX
    grpinveu.b
    grpinveu.p
    grprcan
    3exp2
    mpid
    pm2.43d
    imp
    @3
    @6
    cX
    @4
    cB
    c.pl
    cG
    cX
    c.0
    grpinveu.b
    grpinveu.p
    grpinveu.o
    grplid
    eqeq2d
    bitr3d
    syl5rbb
end
