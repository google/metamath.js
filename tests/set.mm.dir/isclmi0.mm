include "cclm.mm"
include "wcel.mm"
include "cgrp.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "cfv.mm"
include "w3a.mm"
include "c1.mm"
include "cv.mm"
include "wral.mm"
include "caddc.mm"
include "cmul.mm"
include "wa.mm"
include "3pm3.2i.mm"
include "ancoms.mm"
include "3com12.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "jca.mm"
include "3comr.mm"
include "3jca.mm"
include "rgen.mm"
include "isclmp.mm"
include "mpbir2an.mm"

theorem isclmi0
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cK: class K
  let cV: class V
  let cW: class W
  let vr: setvar r
  assume isclmp.t: |- .x. = ( .s ` W )
  assume isclmp.a: |- .+ = ( +g ` W )
  assume isclmp.v: |- V = ( Base ` W )
  assume isclmp.s: |- S = ( Scalar ` W )
  assume isclmp.k: |- K = ( Base ` S )
  assume isclmi0.1: |- S = ( CCfld |`s K )
  assume isclmi0.2: |- W e. Grp
  assume isclmi0.3: |- K e. ( SubRing ` CCfld )
  assume isclmi0.4: |- ( x e. V -> ( 1 .x. x ) = x )
  assume isclmi0.5: |- ( ( y e. K /\ x e. V ) -> ( y .x. x ) e. V )
  assume isclmi0.6: |- ( ( y e. K /\ x e. V /\ z e. V ) -> ( y .x. ( x .+ z ) ) = ( ( y .x. x ) .+ ( y .x. z ) ) )
  assume isclmi0.7: |- ( ( y e. K /\ z e. K /\ x e. V ) -> ( ( z + y ) .x. x ) = ( ( z .x. x ) .+ ( y .x. x ) ) )
  assume isclmi0.8: |- ( ( y e. K /\ z e. K /\ x e. V ) -> ( ( z x. y ) .x. x ) = ( z .x. ( y .x. x ) ) )

  disjoint K x
  disjoint K y
  disjoint K z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint .+ x
  disjoint .+ y
  disjoint .+ z
  disjoint .x. x
  disjoint .x. y
  disjoint .x. z
  disjoint K r
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint S r
  disjoint V r
  disjoint W r
  disjoint .+ r
  disjoint .x. r
  assert |- W e. CMod

  proof
    cW
    cclm
    wcel
    cW
    cgrp
    wcel
    #
    cS
    ccnfld
    cK
    cress
    co
    wceq
    #
    cK
    ccnfld
    csubrg
    cfv
    wcel
    #
    w3a
    c1
    vx
    cv
    #
    c.x
    co
    @3
    wceq
    #
    vy
    cv
    #
    @3
    c.x
    co
    #
    cV
    wcel
    #
    @5
    @3
    vz
    cv
    #
    c.pl
    co
    c.x
    co
    @6
    @5
    @8
    c.x
    co
    c.pl
    co
    wceq
    #
    vz
    cV
    wral
    #
    @8
    @5
    caddc
    co
    @3
    c.x
    co
    @8
    @3
    c.x
    co
    @6
    c.pl
    co
    wceq
    #
    @8
    @5
    cmul
    co
    @3
    c.x
    co
    @8
    @6
    c.x
    co
    wceq
    #
    wa
    #
    vz
    cK
    wral
    #
    w3a
    #
    vy
    cK
    wral
    #
    wa
    #
    vx
    cV
    wral
    @0
    @1
    @2
    isclmi0.2
    isclmi0.1
    isclmi0.3
    3pm3.2i
    @17
    vx
    cV
    @3
    cV
    wcel
    #
    @4
    @16
    isclmi0.4
    @18
    @15
    vy
    cK
    @18
    @5
    cK
    wcel
    #
    wa
    #
    @7
    @10
    @14
    @19
    @18
    @7
    isclmi0.5
    ancoms
    @20
    @9
    vz
    cV
    @18
    @19
    @8
    cV
    wcel
    #
    @9
    @19
    @18
    @21
    @9
    isclmi0.6
    3com12
    3expa
    ralrimiva
    @20
    @13
    vz
    cK
    @18
    @19
    @8
    cK
    wcel
    #
    @13
    @19
    @22
    @18
    @13
    @19
    @22
    @18
    w3a
    @11
    @12
    isclmi0.7
    isclmi0.8
    jca
    3comr
    3expa
    ralrimiva
    3jca
    ralrimiva
    jca
    rgen
    vx
    vy
    vz
    c.pl
    cS
    c.x
    cK
    cV
    cW
    isclmp.t
    isclmp.a
    isclmp.v
    isclmp.s
    isclmp.k
    isclmp
    mpbir2an
end
