include "cgrp.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "c0g.mm"
include "cfv.mm"
include "eqid.mm"
include "grpidcl.mm"
include "wb.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "anbi12d.mm"
include "eqeq2.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "adantl.mm"
include "grpidinv2.mm"
include "ralrimiva.mm"
include "rspcedvd.mm"

theorem grpidinv
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cB: class B
  let c.pl: class .+
  let cG: class G
  assume grpidinv.b: |- B = ( Base ` G )
  assume grpidinv.p: |- .+ = ( +g ` G )

  disjoint G u
  disjoint G x
  disjoint G y
  disjoint u x
  disjoint u y
  disjoint x y
  disjoint B u
  disjoint B y
  disjoint .+ u
  disjoint .+ y
  assert |- ( G e. Grp -> E. u e. B A. x e. B ( ( ( u .+ x ) = x /\ ( x .+ u ) = x ) /\ E. y e. B ( ( y .+ x ) = u /\ ( x .+ y ) = u ) ) )

  proof
    cG
    cgrp
    wcel
    #
    vu
    cv
    #
    vx
    cv
    #
    c.pl
    co
    #
    @2
    wceq
    #
    @2
    @1
    c.pl
    co
    #
    @2
    wceq
    #
    wa
    #
    vy
    cv
    #
    @2
    c.pl
    co
    #
    @1
    wceq
    #
    @2
    @8
    c.pl
    co
    #
    @1
    wceq
    #
    wa
    #
    vy
    cB
    wrex
    #
    wa
    #
    vx
    cB
    wral
    #
    cG
    c0g
    cfv
    #
    @2
    c.pl
    co
    #
    @2
    wceq
    #
    @2
    @17
    c.pl
    co
    #
    @2
    wceq
    #
    wa
    #
    @9
    @17
    wceq
    #
    @11
    @17
    wceq
    #
    wa
    #
    vy
    cB
    wrex
    #
    wa
    #
    vx
    cB
    wral
    #
    vu
    @17
    cB
    cB
    cG
    @17
    grpidinv.b
    @17
    eqid
    #
    grpidcl
    @1
    @17
    wceq
    #
    @16
    @28
    wb
    @0
    @30
    @15
    @27
    vx
    cB
    @30
    @7
    @22
    @14
    @26
    @30
    @4
    @19
    @6
    @21
    @30
    @3
    @18
    @2
    @1
    @17
    @2
    c.pl
    oveq1
    eqeq1d
    @30
    @5
    @20
    @2
    @1
    @17
    @2
    c.pl
    oveq2
    eqeq1d
    anbi12d
    @30
    @13
    @25
    vy
    cB
    @30
    @10
    @23
    @12
    @24
    @1
    @17
    @9
    eqeq2
    @1
    @17
    @11
    eqeq2
    anbi12d
    rexbidv
    anbi12d
    ralbidv
    adantl
    @0
    @27
    vx
    cB
    vy
    @2
    cB
    c.pl
    cG
    @17
    grpidinv.b
    grpidinv.p
    @29
    grpidinv2
    ralrimiva
    rspcedvd
end
