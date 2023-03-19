include "ccvs.mm"
include "wcel.mm"
include "cclm.mm"
include "csca.mm"
include "cfv.mm"
include "cdr.mm"
include "wa.mm"
include "cgrp.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "w3a.mm"
include "c1.mm"
include "cv.mm"
include "wral.mm"
include "caddc.mm"
include "cmul.mm"
include "iscvs.mm"
include "isclmp.mm"
include "anbi2ci.mm"
include "anass.mm"
include "3anan12.mm"
include "anbi2i.mm"
include "eqcomi.mm"
include "eleq1i.mm"
include "anbi1i.mm"
include "3bitr2i.mm"
include "bitr4i.mm"
include "bitri.mm"

theorem iscvsp
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
  assert |- ( W e. CVec <-> ( ( W e. Grp /\ ( S e. DivRing /\ S = ( CCfld |`s K ) ) /\ K e. ( SubRing ` CCfld ) ) /\ A. x e. V ( ( 1 .x. x ) = x /\ A. y e. K ( ( y .x. x ) e. V /\ A. z e. V ( y .x. ( x .+ z ) ) = ( ( y .x. x ) .+ ( y .x. z ) ) /\ A. z e. K ( ( ( z + y ) .x. x ) = ( ( z .x. x ) .+ ( y .x. x ) ) /\ ( ( z x. y ) .x. x ) = ( z .x. ( y .x. x ) ) ) ) ) ) )

  proof
    cW
    ccvs
    wcel
    cW
    cclm
    wcel
    #
    cW
    csca
    cfv
    #
    cdr
    wcel
    #
    wa
    #
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
    #
    c1
    vx
    cv
    #
    c.x
    co
    @10
    wceq
    vy
    cv
    #
    @10
    c.x
    co
    #
    cV
    wcel
    @11
    @10
    vz
    cv
    #
    c.pl
    co
    c.x
    co
    @12
    @11
    @13
    c.x
    co
    c.pl
    co
    wceq
    vz
    cV
    wral
    @13
    @11
    caddc
    co
    @10
    c.x
    co
    @13
    @10
    c.x
    co
    @12
    c.pl
    co
    wceq
    @13
    @11
    cmul
    co
    @10
    c.x
    co
    @13
    @12
    c.x
    co
    wceq
    wa
    vz
    cK
    wral
    w3a
    vy
    cK
    wral
    wa
    vx
    cV
    wral
    #
    wa
    #
    cW
    iscvs
    @3
    @2
    @4
    @6
    @8
    w3a
    #
    @14
    wa
    #
    wa
    @2
    @16
    wa
    #
    @14
    wa
    @15
    @0
    @17
    @2
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
    isclmp
    anbi2ci
    @2
    @16
    @14
    anass
    @18
    @9
    @14
    @18
    @7
    @4
    @8
    wa
    #
    wa
    #
    @9
    @18
    @2
    @6
    @19
    wa
    #
    wa
    @2
    @6
    wa
    #
    @19
    wa
    @20
    @16
    @21
    @2
    @4
    @6
    @8
    3anan12
    anbi2i
    @2
    @6
    @19
    anass
    @22
    @7
    @19
    @2
    @5
    @6
    @1
    cS
    cdr
    cS
    @1
    iscvsp.s
    eqcomi
    eleq1i
    anbi1i
    anbi1i
    3bitr2i
    @4
    @7
    @8
    3anan12
    bitr4i
    anbi1i
    3bitr2i
    bitri
end
