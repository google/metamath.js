include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "grplid.mm"
include "grprid.mm"
include "wral.mm"
include "grplrinv.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "mpan9.mm"
include "jca31.mm"

theorem grpidinv2
  let vy: setvar y
  let cA: class A
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.0: class .0.
  let vx: setvar x
  let vz: setvar z
  assume grplrinv.b: |- B = ( Base ` G )
  assume grplrinv.p: |- .+ = ( +g ` G )
  assume grplrinv.i: |- .0. = ( 0g ` G )

  disjoint B y
  disjoint G y
  disjoint .+ y
  disjoint .0. y
  disjoint A y
  disjoint G x
  disjoint x y
  disjoint A z
  disjoint y z
  disjoint B z
  disjoint G z
  disjoint .+ z
  disjoint .0. z
  assert |- ( ( G e. Grp /\ A e. B ) -> ( ( ( .0. .+ A ) = A /\ ( A .+ .0. ) = A ) /\ E. y e. B ( ( y .+ A ) = .0. /\ ( A .+ y ) = .0. ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cB
    wcel
    #
    wa
    c.0
    cA
    c.pl
    co
    cA
    wceq
    cA
    c.0
    c.pl
    co
    cA
    wceq
    vy
    cv
    #
    cA
    c.pl
    co
    #
    c.0
    wceq
    #
    cA
    @2
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
    #
    cB
    c.pl
    cG
    cA
    c.0
    grplrinv.b
    grplrinv.p
    grplrinv.i
    grplid
    cB
    c.pl
    cG
    cA
    c.0
    grplrinv.b
    grplrinv.p
    grplrinv.i
    grprid
    @0
    @2
    vz
    cv
    #
    c.pl
    co
    #
    c.0
    wceq
    #
    @9
    @2
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
    #
    vz
    cB
    wral
    @1
    @8
    vz
    vy
    cB
    c.pl
    cG
    c.0
    grplrinv.b
    grplrinv.p
    grplrinv.i
    grplrinv
    @15
    @8
    vz
    cA
    cB
    @9
    cA
    wceq
    #
    @14
    @7
    vy
    cB
    @16
    @11
    @4
    @13
    @6
    @16
    @10
    @3
    c.0
    @9
    cA
    @2
    c.pl
    oveq2
    eqeq1d
    @16
    @12
    @5
    c.0
    @9
    cA
    @2
    c.pl
    oveq1
    eqeq1d
    anbi12d
    rexbidv
    rspcv
    mpan9
    jca31
end
