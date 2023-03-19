include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cminusg.mm"
include "cfv.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "adantl.mm"
include "grplinv.mm"
include "grprinv.mm"
include "jca.mm"
include "rspcedvd.mm"
include "ralrimiva.mm"

theorem grplrinv
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.0: class .0.
  assume grplrinv.b: |- B = ( Base ` G )
  assume grplrinv.p: |- .+ = ( +g ` G )
  assume grplrinv.i: |- .0. = ( 0g ` G )

  disjoint B y
  disjoint G x
  disjoint G y
  disjoint x y
  disjoint .+ y
  disjoint .0. y
  assert |- ( G e. Grp -> A. x e. B E. y e. B ( ( y .+ x ) = .0. /\ ( x .+ y ) = .0. ) )

  proof
    cG
    cgrp
    wcel
    #
    vy
    cv
    #
    vx
    cv
    #
    c.pl
    co
    #
    c.0
    wceq
    #
    @2
    @1
    c.pl
    co
    #
    c.0
    wceq
    #
    wa
    #
    vy
    cB
    wrex
    vx
    cB
    @0
    @2
    cB
    wcel
    wa
    #
    @7
    @2
    cG
    cminusg
    cfv
    #
    cfv
    #
    @2
    c.pl
    co
    #
    c.0
    wceq
    #
    @2
    @10
    c.pl
    co
    #
    c.0
    wceq
    #
    wa
    #
    vy
    @10
    cB
    cB
    cG
    @9
    @2
    grplrinv.b
    @9
    eqid
    #
    grpinvcl
    @1
    @10
    wceq
    #
    @7
    @15
    wb
    @8
    @17
    @4
    @12
    @6
    @14
    @17
    @3
    @11
    c.0
    @1
    @10
    @2
    c.pl
    oveq1
    eqeq1d
    @17
    @5
    @13
    c.0
    @1
    @10
    @2
    c.pl
    oveq2
    eqeq1d
    anbi12d
    adantl
    @8
    @12
    @14
    cB
    c.pl
    cG
    @9
    @2
    c.0
    grplrinv.b
    grplrinv.p
    grplrinv.i
    @16
    grplinv
    cB
    c.pl
    cG
    @9
    @2
    c.0
    grplrinv.b
    grplrinv.p
    grplrinv.i
    @16
    grprinv
    jca
    rspcedvd
    ralrimiva
end
