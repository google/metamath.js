include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cplusg.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "cmpt.mm"
include "eqid.mm"
include "cgrp.mm"
include "lmodgrp.mm"
include "adantr.mm"
include "lmodvscl.mm"
include "3expa.mm"
include "fmptd.mm"
include "wceq.mm"
include "lmodvsdi.mm"
include "3exp2.mm"
include "imp43.mm"
include "lmodvacl.mm"
include "3expb.mm"
include "adantlr.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "oveqan12d.mm"
include "adantl.mm"
include "3eqtr4d.mm"
include "isghmd.mm"

theorem lmodvsghm
  let vx: setvar x
  let cR: class R
  let c.x: class .x.
  let cF: class F
  let cK: class K
  let cV: class V
  let cW: class W
  let vy: setvar y
  let vz: setvar z
  assume lmodvsghm.v: |- V = ( Base ` W )
  assume lmodvsghm.f: |- F = ( Scalar ` W )
  assume lmodvsghm.s: |- .x. = ( .s ` W )
  assume lmodvsghm.k: |- K = ( Base ` F )

  disjoint K x
  disjoint R x
  disjoint .x. x
  disjoint V x
  disjoint W x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint R y
  disjoint R z
  disjoint .x. y
  disjoint .x. z
  disjoint V y
  disjoint V z
  disjoint W y
  disjoint W z
  assert |- ( ( W e. LMod /\ R e. K ) -> ( x e. V |-> ( R .x. x ) ) e. ( W GrpHom W ) )

  proof
    cW
    clmod
    wcel
    #
    cR
    cK
    wcel
    #
    wa
    #
    vy
    vz
    cW
    cplusg
    cfv
    #
    @3
    cW
    cW
    vx
    cV
    cR
    vx
    cv
    #
    c.x
    co
    #
    cmpt
    #
    cV
    cV
    lmodvsghm.v
    lmodvsghm.v
    @3
    eqid
    #
    @7
    @0
    cW
    cgrp
    wcel
    @1
    cW
    lmodgrp
    adantr
    #
    @8
    @2
    vx
    cV
    @5
    cV
    @6
    @0
    @1
    @4
    cV
    wcel
    @5
    cV
    wcel
    cR
    c.x
    cF
    cK
    cV
    cW
    @4
    lmodvsghm.v
    lmodvsghm.f
    lmodvsghm.s
    lmodvsghm.k
    lmodvscl
    3expa
    @6
    eqid
    #
    fmptd
    @2
    vy
    cv
    #
    cV
    wcel
    #
    vz
    cv
    #
    cV
    wcel
    #
    wa
    #
    wa
    #
    cR
    @10
    @12
    @3
    co
    #
    c.x
    co
    #
    cR
    @10
    c.x
    co
    #
    cR
    @12
    c.x
    co
    #
    @3
    co
    #
    @16
    @6
    cfv
    #
    @10
    @6
    cfv
    #
    @12
    @6
    cfv
    #
    @3
    co
    #
    @0
    @1
    @11
    @13
    @17
    @20
    wceq
    #
    @0
    @1
    @11
    @13
    @25
    @3
    cR
    c.x
    cF
    cK
    cV
    cW
    @10
    @12
    lmodvsghm.v
    @7
    lmodvsghm.f
    lmodvsghm.s
    lmodvsghm.k
    lmodvsdi
    3exp2
    imp43
    @15
    @16
    cV
    wcel
    #
    @21
    @17
    wceq
    @0
    @14
    @26
    @1
    @0
    @11
    @13
    @26
    @3
    cV
    cW
    @10
    @12
    lmodvsghm.v
    @7
    lmodvacl
    3expb
    adantlr
    vx
    @16
    @5
    @17
    cV
    @6
    @4
    @16
    cR
    c.x
    oveq2
    @9
    cR
    @16
    c.x
    ovex
    fvmpt
    syl
    @14
    @24
    @20
    wceq
    @2
    @11
    @13
    @22
    @18
    @23
    @19
    @3
    vx
    @10
    @5
    @18
    cV
    @6
    @4
    @10
    cR
    c.x
    oveq2
    @9
    cR
    @10
    c.x
    ovex
    fvmpt
    vx
    @12
    @5
    @19
    cV
    @6
    @4
    @12
    cR
    c.x
    oveq2
    @9
    cR
    @12
    c.x
    ovex
    fvmpt
    oveqan12d
    adantl
    3eqtr4d
    isghmd
end
