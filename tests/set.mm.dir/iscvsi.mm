include "ccvs.mm"
include "wcel.mm"
include "cgrp.mm"
include "cdr.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "csubrg.mm"
include "cfv.mm"
include "w3a.mm"
include "c1.mm"
include "cv.mm"
include "wral.mm"
include "caddc.mm"
include "cmul.mm"
include "pm3.2i.mm"
include "3pm3.2i.mm"
include "ancoms.mm"
include "3com12.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "jca.mm"
include "3comr.mm"
include "3jca.mm"
include "rgen.mm"
include "iscvsp.mm"
include "mpbir2an.mm"

theorem iscvsi
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let c.pl: class .+
  let cS: class S
  let c.x: class .x.
  let cK: class K
  let cV: class V
  let cW: class W
  assume iscvsp.t: |- .x. = ( .s ` W )
  assume iscvsp.a: |- .+ = ( +g ` W )
  assume iscvsp.v: |- V = ( Base ` W )
  assume iscvsp.s: |- S = ( Scalar ` W )
  assume iscvsp.k: |- K = ( Base ` S )
  assume iscvsi.1: |- W e. Grp
  assume iscvsi.2: |- S = ( CCfld |`s K )
  assume iscvsi.3: |- S e. DivRing
  assume iscvsi.4: |- K e. ( SubRing ` CCfld )
  assume iscvsi.5: |- ( x e. V -> ( 1 .x. x ) = x )
  assume iscvsi.6: |- ( ( y e. K /\ x e. V ) -> ( y .x. x ) e. V )
  assume iscvsi.7: |- ( ( y e. K /\ x e. V /\ z e. V ) -> ( y .x. ( x .+ z ) ) = ( ( y .x. x ) .+ ( y .x. z ) ) )
  assume iscvsi.8: |- ( ( y e. K /\ z e. K /\ x e. V ) -> ( ( z + y ) .x. x ) = ( ( z .x. x ) .+ ( y .x. x ) ) )
  assume iscvsi.9: |- ( ( y e. K /\ z e. K /\ x e. V ) -> ( ( z x. y ) .x. x ) = ( z .x. ( y .x. x ) ) )

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
  assert |- W e. CVec

  proof
    cW
    ccvs
    wcel
    cW
    cgrp
    wcel
    #
    cS
    cdr
    wcel
    #
    cS
    ccnfld
    cK
    cress
    co
    wceq
    #
    wa
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
    @5
    wceq
    #
    vy
    cv
    #
    @5
    c.x
    co
    #
    cV
    wcel
    #
    @7
    @5
    vz
    cv
    #
    c.pl
    co
    c.x
    co
    @8
    @7
    @10
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
    @10
    @7
    caddc
    co
    @5
    c.x
    co
    @10
    @5
    c.x
    co
    @8
    c.pl
    co
    wceq
    #
    @10
    @7
    cmul
    co
    @5
    c.x
    co
    @10
    @8
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
    @3
    @4
    iscvsi.1
    @1
    @2
    iscvsi.3
    iscvsi.2
    pm3.2i
    iscvsi.4
    3pm3.2i
    @19
    vx
    cV
    @5
    cV
    wcel
    #
    @6
    @18
    iscvsi.5
    @20
    @17
    vy
    cK
    @20
    @7
    cK
    wcel
    #
    wa
    #
    @9
    @12
    @16
    @21
    @20
    @9
    iscvsi.6
    ancoms
    @22
    @11
    vz
    cV
    @20
    @21
    @10
    cV
    wcel
    #
    @11
    @21
    @20
    @23
    @11
    iscvsi.7
    3com12
    3expa
    ralrimiva
    @22
    @15
    vz
    cK
    @20
    @21
    @10
    cK
    wcel
    #
    @15
    @21
    @24
    @20
    @15
    @21
    @24
    @20
    w3a
    @13
    @14
    iscvsi.8
    iscvsi.9
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
    iscvsp.t
    iscvsp.a
    iscvsp.v
    iscvsp.s
    iscvsp.k
    iscvsp
    mpbir2an
end
